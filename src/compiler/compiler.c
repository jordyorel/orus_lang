#include "../../include/compiler.h"

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

#include "../../include/memory.h"
#include "../../include/chunk.h"
#include "../../include/value.h"
#include "../../include/vm.h"
#include "../../include/debug.h"
#include "../../include/scanner.h"
#include "../../include/error.h"

extern VM vm;

static Type* findStructTypeToken(Token token) {
    char name[token.length + 1];
    memcpy(name, token.start, token.length);
    name[token.length] = '\0';
    return findStructType(name);
}

static bool tokenEquals(Token token, const char* str) {
    size_t len = strlen(str);
    return token.length == (int)len && strncmp(token.start, str, len) == 0;
}

static void generateCode(Compiler* compiler, ASTNode* node);
static void addBreakJump(Compiler* compiler, int jumpPos);
static void patchBreakJumps(Compiler* compiler);
static void addContinueJump(Compiler* compiler, int jumpPos);
static void patchContinueJumps(Compiler* compiler);
static void emitForLoop(Compiler* compiler, ASTNode* node);
void disassembleChunk(Chunk* chunk, const char* name);
static void predeclareFunction(Compiler* compiler, ASTNode* node);

static void deduceGenerics(Type* expected, Type* actual,
                           ObjString** names, Type** subs, int count) {
    if (!expected || !actual) return;
    if (expected->kind == TYPE_GENERIC) {
        for (int i = 0; i < count; i++) {
            if (names[i] && strcmp(expected->info.generic.name->chars,
                                  names[i]->chars) == 0) {
                if (!subs[i]) subs[i] = actual;
                return;
            }
        }
        return;
    }
    if (expected->kind != actual->kind) return;
    switch (expected->kind) {
        case TYPE_ARRAY:
            deduceGenerics(expected->info.array.elementType,
                           actual->info.array.elementType,
                           names, subs, count);
            break;
        case TYPE_FUNCTION:
            for (int i = 0; i < expected->info.function.paramCount &&
                            i < actual->info.function.paramCount; i++) {
                deduceGenerics(expected->info.function.paramTypes[i],
                               actual->info.function.paramTypes[i],
                               names, subs, count);
            }
            deduceGenerics(expected->info.function.returnType,
                           actual->info.function.returnType,
                           names, subs, count);
            break;
        case TYPE_STRUCT:
            if (expected->info.structure.fieldCount ==
                actual->info.structure.fieldCount) {
                for (int i = 0; i < expected->info.structure.fieldCount; i++) {
                    deduceGenerics(expected->info.structure.fields[i].type,
                                   actual->info.structure.fields[i].type,
                                   names, subs, count);
                }
            }
            break;
        default:
            break;
    }
}

static void beginScope(Compiler* compiler) { compiler->scopeDepth++; }

static void endScope(Compiler* compiler) {
    removeSymbolsFromScope(&compiler->symbols, compiler->scopeDepth);
    if (compiler->scopeDepth > 0) compiler->scopeDepth--;
}

static void error(Compiler* compiler, const char* message) {
    if (compiler->panicMode) return;
    compiler->panicMode = true;
    fprintf(stderr, "Compiler Error: %s\n", message);
    compiler->hadError = true;
}

static void errorFmt(Compiler* compiler, const char* format, ...) {
    if (compiler->panicMode) return;
    compiler->panicMode = true;
    char buffer[256];
    va_list args;
    va_start(args, format);
    vsnprintf(buffer, sizeof(buffer), format, args);
    va_end(args);
    fprintf(stderr, "Compiler Error: %s\n", buffer);
    compiler->hadError = true;
}




static void writeOp(Compiler* compiler, uint8_t op) {
    writeChunk(compiler->chunk, op, 0);  // Line number could be stored in AST
}

static void writeByte(Compiler* compiler, uint8_t byte) {
    writeChunk(compiler->chunk, byte, 0); // Replace 0 with the appropriate line number if available
}

static int makeConstant(Compiler* compiler, ObjString* string) {
    Value value = STRING_VAL(string);
    int constant = addConstant(compiler->chunk, value);
    return constant;
}

static void emitConstant(Compiler* compiler, Value value) {
    // Ensure constants are emitted with valid values
    // Allow VAL_STRING for now to fix compilation, may need VM changes later.
    if (IS_I32(value) || IS_U32(value) || IS_F64(value) || IS_BOOL(value) || IS_NIL(value) || IS_STRING(value)) {
        if (IS_STRING(value)) {
            ObjString* copy = allocateString(value.as.string->chars,
                                            value.as.string->length);
            value.as.string = copy;
        }
        // fprintf(stderr, "DEBUG: Emitting valid constant: ");
        // printValue(value);
        // fprintf(stderr, "\n");
        writeConstant(compiler->chunk, value, 0);
    } else {
        // fprintf(stderr, "ERROR: Invalid constant type\n");
        // Debug log to trace invalid constants
        // fprintf(stderr, "DEBUG: Invalid constant encountered. Value type: %d\n", value.type);
        // fprintf(stderr, "DEBUG: Value details: ");
        // printValue(value);
        // fprintf(stderr, "\n");
        compiler->hadError = true;
    }
}

static void typeCheckNode(Compiler* compiler, ASTNode* node) {
    if (!node) {
        return;
    }

    switch (node->type) {
        case AST_LITERAL: {
            if (!node->valueType) {
                error(compiler, "Literal node has no type set.");
            }
            break;
        }

        case AST_BINARY: {

            typeCheckNode(compiler, node->left);
            typeCheckNode(compiler, node->right);
            if (compiler->hadError) return;

            Type* leftType = node->left->valueType;
            Type* rightType = node->right->valueType;
            if (!leftType || !rightType) {
                error(compiler, "Binary operand type not set.");
                return;
            }

            TokenType operator= node->data.operation.operator.type;
            switch (operator) {
                case TOKEN_PLUS: {
                    if (leftType->kind == TYPE_STRING || rightType->kind == TYPE_STRING) {
                        node->valueType = getPrimitiveType(TYPE_STRING);
                        node->data.operation.convertLeft = leftType->kind != TYPE_STRING && leftType->kind != TYPE_NIL;
                        node->data.operation.convertRight = rightType->kind != TYPE_STRING && rightType->kind != TYPE_NIL;
                    } else if (leftType->kind == TYPE_F64 || rightType->kind == TYPE_F64) {
                        node->valueType = getPrimitiveType(TYPE_F64);

                        node->data.operation.convertLeft =
                            (leftType->kind == TYPE_I32 || leftType->kind == TYPE_U32);
                        node->data.operation.convertRight =
                            (rightType->kind == TYPE_I32 || rightType->kind == TYPE_U32);
                    } else if (typesEqual(leftType, rightType)) {
                        node->valueType = leftType;
                        node->data.operation.convertLeft = false;
                        node->data.operation.convertRight = false;
                    } else {
                        error(compiler, "Type mismatch in addition operation.");
                        return;
                    }
                    break;
                }
                case TOKEN_MINUS:
                case TOKEN_STAR:
                case TOKEN_SLASH: {
                    // If either operand is a float, the result is a float
                    if (leftType->kind == TYPE_F64 ||
                        rightType->kind == TYPE_F64) {
                        node->valueType = getPrimitiveType(TYPE_F64);

                        // Mark operands for conversion if needed
                        if (leftType->kind == TYPE_I32 || leftType->kind == TYPE_U32) {

                            node->data.operation.convertLeft = true;
                        } else {
                            node->data.operation.convertLeft = false;
                        }

                        if (rightType->kind == TYPE_I32 || rightType->kind == TYPE_U32) {

                            node->data.operation.convertRight = true;
                        } else {
                            node->data.operation.convertRight = false;
                        }
                    }
                    // If both operands are the same type, the result is that type
                    else if (typesEqual(leftType, rightType)) {
                        node->valueType = leftType;
                        node->data.operation.convertLeft = false;
                        node->data.operation.convertRight = false;
                    }
                    // Otherwise, it's a type mismatch
                    else {
                        error(compiler,
                              "Type mismatch in arithmetic operation.");
                        return;
                    }
                    break;
                }

                case TOKEN_MODULO: {
                    if (leftType->kind != TYPE_I32 &&
                        leftType->kind != TYPE_U32) {
                        error(compiler,
                              "Left operand of modulo must be an integer.");
                        return;
                    }
                    if (rightType->kind != TYPE_I32 &&
                        rightType->kind != TYPE_U32) {
                        error(compiler,
                              "Right operand of modulo must be an integer.");
                        return;
                    }
                    node->valueType =
                        leftType;  // Result matches left operand type
                    break;
                }

                case TOKEN_LEFT_BRACKET: {
                    if (leftType->kind != TYPE_ARRAY) {
                        error(compiler, "Can only index arrays.");
                        return;
                    }
                    if (rightType->kind != TYPE_I32 && rightType->kind != TYPE_U32) {
                        error(compiler, "Array index must be an integer.");
                        return;
                    }
                    node->valueType = leftType->info.array.elementType;
                    break;
                }

                // Logical operators
                case TOKEN_AND:
                case TOKEN_OR: {
                    // Both operands must be boolean
                    if (leftType->kind != TYPE_BOOL) {
                        error(compiler, "Left operand of logical operator must be a boolean.");
                        return;
                    }
                    if (rightType->kind != TYPE_BOOL) {
                        error(compiler, "Right operand of logical operator must be a boolean.");
                        return;
                    }
                    // Logical operators return a boolean
                    node->valueType = getPrimitiveType(TYPE_BOOL);
                    break;
                }

                // Comparison operators
                case TOKEN_LESS:
                case TOKEN_LESS_EQUAL:
                case TOKEN_GREATER:
                case TOKEN_GREATER_EQUAL:
                case TOKEN_EQUAL_EQUAL:
                case TOKEN_BANG_EQUAL: {
                    // Comparison operators always return a boolean
                    node->valueType = getPrimitiveType(TYPE_BOOL);
                    break;
                }

                default:
                    error(compiler,
                          "Unsupported binary operator in type checker.");
                    return;
            }
            break;
        }

        case AST_UNARY: {
            typeCheckNode(compiler, node->left);
            if (compiler->hadError) return;

            Type* operandType = node->left->valueType;
            if (!operandType) {
                error(compiler, "Unary operand type not set.");
                return;
            }

            TokenType operator= node->data.operation.operator.type;
            switch (operator) {
                case TOKEN_MINUS:
                    if (operandType->kind != TYPE_I32 &&
                        operandType->kind != TYPE_U32 &&
                        operandType->kind != TYPE_F64) {
                        error(compiler,
                              "Unary minus operand must be a number.");
                        return;
                    }
                    node->valueType = operandType;
                    break;

                case TOKEN_NOT:
                    if (operandType->kind != TYPE_BOOL) {
                        error(compiler, "Unary not operand must be a boolean.");
                        return;
                    }
                    node->valueType = getPrimitiveType(TYPE_BOOL);
                    break;

                default:
                    error(compiler, "Unsupported unary operator.");
                    return;
            }
            break;
        }

        case AST_VARIABLE: {
            uint8_t index = resolveVariable(compiler, node->data.variable.name);
            if (index == UINT8_MAX) {
                char tempName[node->data.variable.name.length + 1];
                memcpy(tempName, node->data.variable.name.start,
                       node->data.variable.name.length);
                tempName[node->data.variable.name.length] = '\0';
                Symbol* any = findAnySymbol(&compiler->symbols, tempName);
                if (any && !any->active) {
                    emitUndefinedVarError(compiler,
                                         &node->data.variable.name,
                                         &any->token,
                                         tempName);
                } else {
                    emitUndefinedVarError(compiler,
                                         &node->data.variable.name,
                                         NULL,
                                         tempName);
                }
                return;
            }
            node->data.variable.index = index;
            node->valueType = variableTypes[index];
            if (!node->valueType) {
                error(compiler, "Variable has no type defined.");
                return;
            }
            break;
        }

        case AST_LET: {
            // First type check the initializer if present
            if (node->data.let.initializer) {
                typeCheckNode(compiler, node->data.let.initializer);
                if (compiler->hadError) return;
            }

            Type* initType = NULL;
            Type* declType = node->data.let.type;

            if (node->data.let.initializer) {
                initType = node->data.let.initializer->valueType;
                if (!initType) {
                    error(compiler, "Could not determine initializer type");
                    return;
                }
            }

            if (declType) {
                if (initType) {
                    // Allow i32 literals to be used for u32 variables if the value is non-negative
                    if (declType->kind == TYPE_U32 && initType->kind == TYPE_I32) {
                        if (IS_I32(node->data.let.initializer->data.literal) &&
                            AS_I32(node->data.let.initializer->data.literal) >= 0) {
                            // Convert the literal to u32
                            int32_t value = AS_I32(node->data.let.initializer->data.literal);
                            node->data.let.initializer->data.literal = U32_VAL((uint32_t)value);
                            node->data.let.initializer->valueType = declType;
                            initType = declType;
                        }
                    }
                    // Allow i32/u32 literals to be used for f64 variables
                    else if (declType->kind == TYPE_F64 &&
                            (initType->kind == TYPE_I32 || initType->kind == TYPE_U32)) {
                        if (IS_I32(node->data.let.initializer->data.literal)) {
                            int32_t value = AS_I32(node->data.let.initializer->data.literal);
                            node->data.let.initializer->data.literal = F64_VAL((double)value);
                            node->data.let.initializer->valueType = declType;
                            initType = declType;
                        } else if (IS_U32(node->data.let.initializer->data.literal)) {
                            uint32_t value = AS_U32(node->data.let.initializer->data.literal);
                            node->data.let.initializer->data.literal = F64_VAL((double)value);
                            node->data.let.initializer->valueType = declType;
                            initType = declType;
                        }
                    }
                    if (!typesEqual(declType, initType)) {
                        if (initType->kind == TYPE_ARRAY &&
                            initType->info.array.elementType->kind == TYPE_NIL &&
                            declType->kind == TYPE_ARRAY) {
                            node->data.let.initializer->valueType = declType;
                            initType = declType;
                        } else {
                            error(compiler, "Type mismatch in let declaration.");
                            return;
                        }
                    }
                }
                node->valueType = declType;
            } else if (initType) {
                node->valueType = initType;
            } else {
                error(compiler, "Cannot determine variable type");
                return;
            }

            // Add the variable to the symbol table
            uint8_t index = addLocal(compiler, node->data.let.name, node->valueType);
            node->data.let.index = index;
            break;
        }

        case AST_PRINT: {
            ASTNode* format = node->data.print.format;
            ASTNode* arg = node->data.print.arguments;
            
            // Type check the format expression first
            typeCheckNode(compiler, format);
            if (compiler->hadError) return;
            
            if (arg != NULL) {
                // This is a formatted print with interpolation
                // Verify format is a string
                if (format->valueType == NULL || format->valueType->kind != TYPE_STRING) {
                    error(compiler, "First argument to print must evaluate to a string for interpolation.");
                    return;
                }

                // Count arguments safely and validate linked list
                ASTNode* current = arg;
                while (current != NULL) {
                    if (current == current->next) {
                        compiler->hadError = true;
                        return;
                    }

                    typeCheckNode(compiler, current);  // Perform type check
                    if (compiler->hadError) return;

                    current = current->next;
                }
            } else {
                // This is a simple print, format can be any type
                // No additional type checking needed
            }

            break;
        }

        case AST_ASSIGNMENT: {
            // First type check the value expression
            if (node->left) {
                typeCheckNode(compiler, node->left);
                if (compiler->hadError) return;
            } else {
                error(compiler, "Assignment requires a value expression");
                return;
            }

            // Resolve the variable being assigned to
            uint8_t index = resolveVariable(compiler, node->data.variable.name);
            if (index == UINT8_MAX) {
                char tempName[node->data.variable.name.length + 1];
                memcpy(tempName, node->data.variable.name.start,
                       node->data.variable.name.length);
                tempName[node->data.variable.name.length] = '\0';
                errorFmt(compiler, "Cannot assign to undefined variable '%s'.",
                        tempName);
                return;
            }
            node->data.variable.index = index;

            // Check that the types are compatible
            Type* varType = variableTypes[index];
            Type* valueType = node->left->valueType;

            if (!varType) {
                error(compiler, "Variable has no type defined.");
                return;
            }

            if (!valueType) {
                error(compiler, "Could not determine value type.");
                return;
            }

            // Allow i32 literals to be used for u32 variables if the value is non-negative
            if (varType->kind == TYPE_U32 && valueType->kind == TYPE_I32 &&
                node->left->type == AST_LITERAL) {
                if (IS_I32(node->left->data.literal) &&
                    AS_I32(node->left->data.literal) >= 0) {
                    // Convert the literal to u32
                    int32_t value = AS_I32(node->left->data.literal);
                    node->left->data.literal = U32_VAL((uint32_t)value);
                    node->left->valueType = varType;
                    valueType = varType;
                }
            }
            // Allow i32/u32 literals to be used for f64 variables
            else if (varType->kind == TYPE_F64 &&
                    (valueType->kind == TYPE_I32 || valueType->kind == TYPE_U32) &&
                    node->left->type == AST_LITERAL) {
                if (IS_I32(node->left->data.literal)) {
                    int32_t value = AS_I32(node->left->data.literal);
                    node->left->data.literal = F64_VAL((double)value);
                    node->left->valueType = varType;
                    valueType = varType;
                } else if (IS_U32(node->left->data.literal)) {
                    uint32_t value = AS_U32(node->left->data.literal);
                    node->left->data.literal = F64_VAL((double)value);
                    node->left->valueType = varType;
                    valueType = varType;
                }
            }

            if (!typesEqual(varType, valueType)) {
                if (valueType->kind == TYPE_ARRAY &&
                    valueType->info.array.elementType->kind == TYPE_NIL &&
                    varType->kind == TYPE_ARRAY) {
                    node->left->valueType = varType;
                    valueType = varType;
                } else {
                    error(compiler, "Type mismatch in assignment.");
                    return;
                }
            }

            // The assignment expression has the same type as the variable
            node->valueType = varType;
            break;
        }

        case AST_IF: {
            // Type check the condition
            typeCheckNode(compiler, node->data.ifStmt.condition);
            if (compiler->hadError) return;

            // Ensure the condition is a boolean
            Type* condType = node->data.ifStmt.condition->valueType;
            if (!condType || condType->kind != TYPE_BOOL) {
                error(compiler, "If condition must be a boolean expression.");
                return;
            }

            // Type check the then branch
            typeCheckNode(compiler, node->data.ifStmt.thenBranch);
            if (compiler->hadError) return;

            // Type check the elif conditions and branches
            ASTNode* elifCondition = node->data.ifStmt.elifConditions;
            ASTNode* elifBranch = node->data.ifStmt.elifBranches;
            while (elifCondition != NULL && elifBranch != NULL) {
                // Type check the elif condition
                typeCheckNode(compiler, elifCondition);
                if (compiler->hadError) return;

                // Ensure the elif condition is a boolean
                Type* elifCondType = elifCondition->valueType;
                if (!elifCondType || elifCondType->kind != TYPE_BOOL) {
                    error(compiler, "Elif condition must be a boolean expression.");
                    return;
                }

                // Type check the elif branch
                typeCheckNode(compiler, elifBranch);
                if (compiler->hadError) return;

                // Move to the next elif condition and branch
                elifCondition = elifCondition->next;
                elifBranch = elifBranch->next;
            }

            // Type check the else branch if it exists
            if (node->data.ifStmt.elseBranch) {
                typeCheckNode(compiler, node->data.ifStmt.elseBranch);
                if (compiler->hadError) return;
            }

            // If statements don't have a value type
            node->valueType = NULL;
            break;
        }

        case AST_BLOCK: {
            if (node->data.block.scoped) {
                beginScope(compiler);
            }

            // Type check each statement in the block
            ASTNode* stmt = node->data.block.statements;
            while (stmt) {
                typeCheckNode(compiler, stmt);
                if (compiler->hadError) {
                    if (node->data.block.scoped) endScope(compiler);
                    return;
                }
                stmt = stmt->next;
            }

            if (node->data.block.scoped) {
                endScope(compiler);
            }

            // Blocks don't have a value type
            node->valueType = NULL;
            break;
        }

        case AST_WHILE: {
            // Type check the condition
            typeCheckNode(compiler, node->data.whileStmt.condition);
            if (compiler->hadError) return;

            // Ensure the condition is a boolean
            Type* condType = node->data.whileStmt.condition->valueType;
            if (!condType || condType->kind != TYPE_BOOL) {
                error(compiler, "While condition must be a boolean expression.");
                return;
            }

            beginScope(compiler);
            // Type check the body
            typeCheckNode(compiler, node->data.whileStmt.body);
            if (compiler->hadError) {
                endScope(compiler);
                return;
            }
            endScope(compiler);

            // While statements don't have a value type
            node->valueType = NULL;
            break;
        }

        case AST_FOR: {
            // Type check the range start expression
            typeCheckNode(compiler, node->data.forStmt.startExpr);
            if (compiler->hadError) return;

            // Type check the range end expression
            typeCheckNode(compiler, node->data.forStmt.endExpr);
            if (compiler->hadError) return;

            // Type check the step expression if it exists
            if (node->data.forStmt.stepExpr) {
                typeCheckNode(compiler, node->data.forStmt.stepExpr);
                if (compiler->hadError) return;
            }

            // Ensure the range expressions are integers
            Type* startType = node->data.forStmt.startExpr->valueType;
            Type* endType = node->data.forStmt.endExpr->valueType;
            Type* stepType = node->data.forStmt.stepExpr ? node->data.forStmt.stepExpr->valueType : NULL;

            if (!startType || (startType->kind != TYPE_I32 && startType->kind != TYPE_U32)) {
                error(compiler, "For loop range start must be an integer.");
                return;
            }

            if (!endType || (endType->kind != TYPE_I32 && endType->kind != TYPE_U32)) {
                error(compiler, "For loop range end must be an integer.");
                return;
            }

            if (stepType && (stepType->kind != TYPE_I32 && stepType->kind != TYPE_U32)) {
                error(compiler, "For loop step must be an integer.");
                return;
            }

            beginScope(compiler);
            // Define the iterator variable
            uint8_t index = defineVariable(compiler, node->data.forStmt.iteratorName, startType);
            node->data.forStmt.iteratorIndex = index;

            // Type check the body
            typeCheckNode(compiler, node->data.forStmt.body);
            if (compiler->hadError) {
                endScope(compiler);
                return;
            }
            endScope(compiler);

            // For statements don't have a value type
            node->valueType = NULL;
            break;
        }

        case AST_FUNCTION: {
            uint8_t index = node->data.function.index;
            if (index == UINT8_MAX) {
                predeclareFunction(compiler, node);
                index = node->data.function.index;
            }

            beginScope(compiler);
            // Type check parameters
            ASTNode* param = node->data.function.parameters;
            while (param != NULL) {
                typeCheckNode(compiler, param);
                if (compiler->hadError) {
                    endScope(compiler);
                    return;
                }
                param = param->next;
            }

            // Type check the function body
            typeCheckNode(compiler, node->data.function.body);
            if (compiler->hadError) {
                endScope(compiler);
                return;
            }
            endScope(compiler);

            // Function declarations don't have a value type
            node->valueType = NULL;
            break;
        }

       case AST_CALL: {
            // Attempt to resolve the function name
            ObjString* nameObj = allocateString(node->data.call.name.start,
                                               node->data.call.name.length);
            int nativeIdx = findNative(nameObj);
            node->data.call.nativeIndex = nativeIdx;
            // Built-in functions
            if (tokenEquals(node->data.call.name, "len")) {
                if (node->data.call.argCount != 1) {
                    error(compiler, "len() takes exactly one argument.");
                    return;
                }
                ASTNode* arg = node->data.call.arguments;
                typeCheckNode(compiler, arg);
                if (compiler->hadError) return;
                if (!arg->valueType ||
                    (arg->valueType->kind != TYPE_ARRAY &&
                     arg->valueType->kind != TYPE_STRING)) {
                    error(compiler, "len() expects array or string.");
                    return;
                }
                node->valueType = getPrimitiveType(TYPE_I32);
                break;
            } else if (tokenEquals(node->data.call.name, "substring")) {
                if (node->data.call.argCount != 3) {
                    error(compiler, "substring() takes exactly three arguments.");
                    return;
                }
                ASTNode* strArg = node->data.call.arguments;
                ASTNode* startArg = strArg->next;
                ASTNode* lenArg = startArg->next;
                typeCheckNode(compiler, strArg);
                typeCheckNode(compiler, startArg);
                typeCheckNode(compiler, lenArg);
                if (compiler->hadError) return;
                if (!strArg->valueType || strArg->valueType->kind != TYPE_STRING) {
                    error(compiler, "substring() first argument must be a string.");
                    return;
                }
                if (!startArg->valueType || startArg->valueType->kind != TYPE_I32) {
                    error(compiler, "substring() second argument must be i32.");
                    return;
                }
                if (!lenArg->valueType || lenArg->valueType->kind != TYPE_I32) {
                    error(compiler, "substring() third argument must be i32.");
                    return;
                }
                node->valueType = getPrimitiveType(TYPE_STRING);
                break;
            } else if (tokenEquals(node->data.call.name, "type")) {
                if (node->data.call.argCount != 1) {
                    error(compiler, "type() takes exactly one argument.");
                    return;
                }
                ASTNode* valArg = node->data.call.arguments;
                typeCheckNode(compiler, valArg);
                if (compiler->hadError) return;
                node->valueType = getPrimitiveType(TYPE_STRING);
                break;
            } else if (tokenEquals(node->data.call.name, "is_type")) {
                if (node->data.call.argCount != 2) {
                    error(compiler, "is_type() takes exactly two arguments.");
                    return;
                }
                ASTNode* valArg = node->data.call.arguments;
                ASTNode* typeArg = valArg->next;
                typeCheckNode(compiler, valArg);
                typeCheckNode(compiler, typeArg);
                if (compiler->hadError) return;
                if (!typeArg->valueType || typeArg->valueType->kind != TYPE_STRING) {
                    error(compiler, "is_type() second argument must be string.");
                    return;
                }
                node->valueType = getPrimitiveType(TYPE_BOOL);
                break;
            } else if (tokenEquals(node->data.call.name, "push") &&
                       node->data.call.argCount == 2) {
                ASTNode* arr = node->data.call.arguments;
                ASTNode* val = arr->next;
                typeCheckNode(compiler, arr);
                typeCheckNode(compiler, val);
                if (compiler->hadError) return;
                if (arr->valueType && arr->valueType->kind == TYPE_ARRAY) {
                    Type* elemType = arr->valueType->info.array.elementType;
                    if (elemType->kind == TYPE_NIL) {
                        arr->valueType = createArrayType(val->valueType);
                        elemType = val->valueType;
                        if (arr->type == AST_VARIABLE) {
                            variableTypes[arr->data.variable.index] = arr->valueType;
                        }
                    }
                    if (!typesEqual(elemType, val->valueType)) {
                        error(compiler, "push() value type mismatch.");
                        return;
                    }
                    node->valueType = arr->valueType;
                    break;
                }
                // Not an array: likely a method call, fall through
            } else if (tokenEquals(node->data.call.name, "pop") &&
                       node->data.call.argCount == 1) {
                ASTNode* arr = node->data.call.arguments;
                typeCheckNode(compiler, arr);
                if (compiler->hadError) return;
                if (arr->valueType && arr->valueType->kind == TYPE_ARRAY) {
                    node->valueType = arr->valueType->info.array.elementType;
                    break;
                }
                // Not an array: treat as normal call
            }

            uint8_t index = resolveVariable(compiler, node->data.call.name);

            // Type check arguments first to know the type of the receiver
            ASTNode* arg = node->data.call.arguments;
            while (arg != NULL) {
                typeCheckNode(compiler, arg);
                if (compiler->hadError) return;
                arg = arg->next;
            }

            // If call specifies a static struct type, try mangled name first
            if (node->data.call.staticType != NULL) {
                const char* structName = node->data.call.staticType->info.structure.name->chars;
                size_t structLen = strlen(structName);
                size_t nameLen = node->data.call.name.length;
                char* temp = (char*)malloc(structLen + 1 + nameLen + 1);
                memcpy(temp, structName, structLen);
                temp[structLen] = '_';
                memcpy(temp + structLen + 1, node->data.call.name.start, nameLen);
                temp[structLen + 1 + nameLen] = '\0';
                Symbol* sym = findSymbol(&compiler->symbols, temp);
                if (sym) {
                    index = sym->index;
                    ObjString* fullStr = allocateString(temp, structLen + 1 + nameLen);
                    node->data.call.name.start = fullStr->chars;
                    node->data.call.name.length = structLen + 1 + nameLen;
                    node->data.call.mangledName = fullStr;
                }
                free(temp);
            } else if (index == UINT8_MAX && node->data.call.arguments != NULL) {
                // If not found, try mangled method name based on first argument (instance method)
                ASTNode* recv = node->data.call.arguments;
                Type* recvType = recv->valueType;
                if (recvType && recvType->kind == TYPE_STRUCT) {
                    const char* structName = recvType->info.structure.name->chars;
                    size_t structLen = strlen(structName);
                    size_t nameLen = node->data.call.name.length;
                    char* temp = (char*)malloc(structLen + 1 + nameLen + 1);
                    memcpy(temp, structName, structLen);
                    temp[structLen] = '_';
                    memcpy(temp + structLen + 1, node->data.call.name.start, nameLen);
                    temp[structLen + 1 + nameLen] = '\0';
                    Symbol* sym = findSymbol(&compiler->symbols, temp);
                    if (sym) {
                        index = sym->index;
                        ObjString* fullStr = allocateString(temp, structLen + 1 + nameLen);
                        node->data.call.name.start = fullStr->chars;
                        node->data.call.name.length = structLen + 1 + nameLen;
                        node->data.call.mangledName = fullStr;
                    }
                    free(temp);
                }
            }

            if (index == UINT8_MAX) {
                emitUndefinedFunctionError(compiler, &node->data.call.name);
                return;
            }

            node->data.call.index = index;

            // Get the function's return type
            Type* funcType = variableTypes[index];
            if (!funcType || funcType->kind != TYPE_FUNCTION) {
                error(compiler, "Called object is not a function.");
                return;
            }

            ASTNode* fnNode = vm.functionDecls[index];
            ObjString** gnames = NULL;
            int gcount = 0;
            if (fnNode) {
                gnames = fnNode->data.function.genericParams;
                gcount = fnNode->data.function.genericCount;
            }
            Type** gsubs = NULL;
            if (gcount > 0) {
                gsubs = (Type**)calloc(gcount, sizeof(Type*));
                if (node->data.call.genericArgCount > 0) {
                    if (node->data.call.genericArgCount != gcount) {
                        char msgBuffer[128];
                        snprintf(msgBuffer, sizeof(msgBuffer),
        "generic argument count mismatch: expected %d, found %d",
        gcount, node->data.call.genericArgCount);
    char helpBuffer[128];
    snprintf(helpBuffer, sizeof(helpBuffer),
        "function expects %d generic type parameter(s), but %d were provided",
        gcount, node->data.call.genericArgCount);
    const char* note = "Check the function definition and provide the correct number of generic arguments.";
    emitGenericTypeError(compiler, &node->data.call.name, msgBuffer, helpBuffer, note);
    return;
                    }
                    for (int i = 0; i < gcount; i++) gsubs[i] = node->data.call.genericArgs[i];
                }
            }

            ASTNode* argIt = node->data.call.arguments;
            ASTNode* argNodes[256];
            int acount = 0;
            while (argIt != NULL && acount < 256) {
                argNodes[acount++] = argIt;
                argIt = argIt->next;
            }

            for (int i = 0; i < funcType->info.function.paramCount; i++) {
                Type* expected = funcType->info.function.paramTypes[i];
                if (gcount > 0 && i < acount) {
                    deduceGenerics(expected, argNodes[i]->valueType,
                                   gnames, gsubs, gcount);
                }
                if (gcount > 0) {
                    expected = substituteGenerics(expected, gnames, gsubs, gcount);
                }
                if (i >= acount || !typesEqual(expected, argNodes[i]->valueType)) {
                    const char* expectedType = getTypeName(expected->kind);
                    const char* actualType = argNodes[i] && argNodes[i]->valueType ? getTypeName(argNodes[i]->valueType->kind) : "(none)";
                    emitTypeMismatchError(compiler, &node->data.call.name, expectedType, actualType);
                    return;
                }
            }

            Type* returnType = substituteGenerics(funcType->info.function.returnType,
                                                 gnames, gsubs, gcount);

            node->data.call.convertArgs = (bool*)calloc(node->data.call.argCount, sizeof(bool));
            node->valueType = returnType;
            break;
        }

        case AST_ARRAY: {
            ASTNode* elem = node->data.array.elements;
            Type* elementType = NULL;
            while (elem) {
                typeCheckNode(compiler, elem);
                if (compiler->hadError) return;
                if (!elementType)
                    elementType = elem->valueType;
                else if (!typesEqual(elementType, elem->valueType)) {
                    error(compiler, "Array elements must have the same type.");
                    return;
                }
                elem = elem->next;
            }
            if (!elementType) {
                node->valueType = createArrayType(getPrimitiveType(TYPE_NIL));
            } else {
                node->valueType = createArrayType(elementType);
            }
            break;
        }

        case AST_STRUCT_LITERAL: {
            Type* structType = findStructTypeToken(node->data.structLiteral.name);
            if (!structType) {
                error(compiler, "Unknown struct type.");
                return;
            }
            if (node->data.structLiteral.genericArgCount > 0) {
                structType = instantiateStructType(structType,
                                                  node->data.structLiteral.genericArgs,
                                                  node->data.structLiteral.genericArgCount);
            }
            if (structType->info.structure.fieldCount !=
                node->data.structLiteral.fieldCount) {
                error(compiler, "Struct literal field count mismatch.");
                return;
            }
            ASTNode* value = node->data.structLiteral.values;
            for (int i = 0; i < node->data.structLiteral.fieldCount; i++) {
                if (!value) {
                    error(compiler, "Missing struct field value.");
                    return;
                }
                typeCheckNode(compiler, value);
                if (compiler->hadError) return;
                if (value->type == AST_ARRAY && value->valueType &&
                    value->valueType->kind == TYPE_ARRAY &&
                    value->valueType->info.array.elementType->kind == TYPE_NIL &&
                    structType->info.structure.fields[i].type->kind == TYPE_ARRAY) {
                    value->valueType = structType->info.structure.fields[i].type;
                }
                if (!typesEqual(structType->info.structure.fields[i].type,
                                value->valueType)) {
                    const char* structName = structType->info.structure.name->chars;
                    const char* fieldName = structType->info.structure.fields[i].name->chars;
                    const char* expectedType = getTypeName(structType->info.structure.fields[i].type->kind);
                    const char* actualType = value->valueType ? getTypeName(value->valueType->kind) : "(none)";
                    emitStructFieldTypeMismatchError(compiler, &node->data.structLiteral.name, structName, fieldName, expectedType, actualType);
                    return;
                }
                value = value->next;
            }
            node->valueType = structType;
            break;
        }

        case AST_FIELD: {
            typeCheckNode(compiler, node->left);
            if (compiler->hadError) return;
            Type* structType = node->left->valueType;
            if (!structType || structType->kind != TYPE_STRUCT) {
                const char* actualType = structType ? getTypeName(structType->kind) : "(none)";
                emitFieldAccessNonStructError(compiler, &node->data.field.fieldName, actualType);
                return;
            }
            int index = -1;
            for (int i = 0; i < structType->info.structure.fieldCount; i++) {
                if (strncmp(structType->info.structure.fields[i].name->chars,
                            node->data.field.fieldName.start,
                            node->data.field.fieldName.length) == 0 &&
                    structType->info.structure.fields[i].name->chars
                        [node->data.field.fieldName.length] == '\0') {
                    index = i;
                    break;
                }
            }
            if (index < 0) {
                error(compiler, "Unknown field name.");
                return;
            }
            node->data.field.index = index;
            node->valueType = structType->info.structure.fields[index].type;
            break;
        }

        case AST_FIELD_SET: {
            typeCheckNode(compiler, node->right); // object
            if (compiler->hadError) return;
            Type* structType = node->right->valueType;
            if (!structType || structType->kind != TYPE_STRUCT) {
                error(compiler, "Can only set fields on structs.");
                return;
            }
            int index = -1;
            for (int i = 0; i < structType->info.structure.fieldCount; i++) {
                if (strncmp(structType->info.structure.fields[i].name->chars,
                            node->data.fieldSet.fieldName.start,
                            node->data.fieldSet.fieldName.length) == 0 &&
                    structType->info.structure.fields[i].name->chars
                        [node->data.fieldSet.fieldName.length] == '\0') {
                    index = i;
                    break;
                }
            }
            if (index < 0) {
                error(compiler, "Unknown field name.");
                return;
            }
            node->data.fieldSet.index = index;
            typeCheckNode(compiler, node->left); // value
            if (compiler->hadError) return;
            if (!typesEqual(structType->info.structure.fields[index].type,
                            node->left->valueType)) {
                error(compiler, "Type mismatch in field assignment.");
                return;
            }
            node->valueType = structType->info.structure.fields[index].type;
            break;
        }

        case AST_ARRAY_SET: {
            typeCheckNode(compiler, node->right);  // array expression
            if (compiler->hadError) return;
            typeCheckNode(compiler, node->data.arraySet.index);
            if (compiler->hadError) return;
            typeCheckNode(compiler, node->left);  // value
            if (compiler->hadError) return;

            Type* arrayType = node->right->valueType;
            Type* indexType = node->data.arraySet.index->valueType;
            Type* valueType = node->left->valueType;
            if (!arrayType || arrayType->kind != TYPE_ARRAY) {
                error(compiler, "Can only assign to array elements.");
                return;
            }
            if (!indexType || (indexType->kind != TYPE_I32 && indexType->kind != TYPE_U32)) {
                error(compiler, "Array index must be an integer.");
                return;
            }
            Type* elementType = arrayType->info.array.elementType;
            if (!typesEqual(elementType, valueType)) {
                error(compiler, "Type mismatch in array assignment.");
                return;
            }
            node->valueType = elementType;
            break;
        }

        case AST_SLICE: {
            typeCheckNode(compiler, node->left); // array
            typeCheckNode(compiler, node->data.slice.start);
            typeCheckNode(compiler, node->data.slice.end);
            if (compiler->hadError) return;
            Type* arrayType = node->left->valueType;
            Type* startType = node->data.slice.start->valueType;
            Type* endType = node->data.slice.end->valueType;
            if (!arrayType || arrayType->kind != TYPE_ARRAY) {
                error(compiler, "Can only slice arrays.");
                return;
            }
            if (!startType || (startType->kind != TYPE_I32 && startType->kind != TYPE_U32)) {
                error(compiler, "Slice start index must be an integer.");
                return;
            }
            if (!endType || (endType->kind != TYPE_I32 && endType->kind != TYPE_U32)) {
                error(compiler, "Slice end index must be an integer.");
                return;
            }
            node->valueType = node->left->valueType;
            break;
        }

        case AST_RETURN: {
            // Type check the return value if present
            if (node->data.returnStmt.value != NULL) {
                typeCheckNode(compiler, node->data.returnStmt.value);
                if (compiler->hadError) return;
            }

            // Return statements don't have a value type
            node->valueType = NULL;
            break;
        }

        case AST_BREAK: {
            // Break statements don't have a value type
            node->valueType = NULL;
            break;
        }

        case AST_CONTINUE: {
            // Continue statements don't have a value type
            node->valueType = NULL;
            break;
        }

        case AST_IMPORT: {
            node->valueType = NULL;
            break;
        }

        case AST_TRY: {
            beginScope(compiler);
            Type* strType = getPrimitiveType(TYPE_STRING);
            uint8_t idx = addLocal(compiler, node->data.tryStmt.errorName, strType);
            node->data.tryStmt.errorIndex = idx;
            typeCheckNode(compiler, node->data.tryStmt.tryBlock);
            if (compiler->hadError) { endScope(compiler); return; }
            typeCheckNode(compiler, node->data.tryStmt.catchBlock);
            endScope(compiler);
            node->valueType = NULL;
            break;
        }

        default:
            error(compiler, "Unsupported AST node type in type checker.");
            break;
    }
}

static void generateCode(Compiler* compiler, ASTNode* node) {
    if (!node || compiler->hadError) {
        return;
    }

    switch (node->type) {
        case AST_LITERAL: {
            // Debug log to trace AST nodes generating constants
            // fprintf(stderr, "DEBUG: Generating constant from AST node of type: %d\n", node->type);
            if (node->type == AST_LITERAL) {
                // fprintf(stderr, "DEBUG: Literal value: ");
                // printValue(node->data.literal);
                // fprintf(stderr, "\n");
            }
            emitConstant(compiler, node->data.literal);
            break;
        }

        case AST_BINARY: {

            // Generate code for the left operand
            generateCode(compiler, node->left);
            if (compiler->hadError) return;

            // Convert left operand to result type before generating the right
            if (node->data.operation.convertLeft) {
                Type* leftType = node->left->valueType;
                TypeKind resultType = node->valueType->kind;

                switch (resultType) {
                    case TYPE_F64:
                        if (leftType->kind == TYPE_I32)
                            writeOp(compiler, OP_I32_TO_F64);
                        else if (leftType->kind == TYPE_U32)
                            writeOp(compiler, OP_U32_TO_F64);
                        else {
                            char msgBuffer[256];
                            const char* leftTypeName = getTypeName(leftType->kind);
                            snprintf(msgBuffer, sizeof(msgBuffer),
                                "Unsupported left operand conversion for binary operation. Left type: '%s', operation at line %d",
                                leftTypeName, node->data.operation.operator.line);
                            error(compiler, msgBuffer);
                            return;
                        }
                        break;
                    case TYPE_STRING:
                        switch (leftType->kind) {
                            case TYPE_I32: writeOp(compiler, OP_I32_TO_STRING); break;
                            case TYPE_U32: writeOp(compiler, OP_U32_TO_STRING); break;
                            case TYPE_F64: writeOp(compiler, OP_F64_TO_STRING); break;
                            case TYPE_BOOL: writeOp(compiler, OP_BOOL_TO_STRING); break;
                            case TYPE_ARRAY: writeOp(compiler, OP_ARRAY_TO_STRING); break;
                            case TYPE_STRUCT: writeOp(compiler, OP_ARRAY_TO_STRING); break;
                            default:
                                error(compiler,
                                      "Unsupported left operand conversion for binary operation.");
                                return;
                        }
                        break;
                    default:
                        error(compiler, "Unsupported result type for binary operation.");
                        return;
                }
            }

            // Generate code for the right operand
            generateCode(compiler, node->right);
            if (compiler->hadError) return;

            // Get operand and result types
            Type* leftType = node->left->valueType;
            Type* rightType = node->right->valueType;
            TypeKind resultType = node->valueType->kind;

            // Convert right operand to result type if needed
            if (node->data.operation.convertRight) {

                switch (resultType) {
                    case TYPE_F64:
                        if (rightType->kind == TYPE_I32)
                            writeOp(compiler, OP_I32_TO_F64);
                        else if (rightType->kind == TYPE_U32)
                            writeOp(compiler, OP_U32_TO_F64);
                        else {
                            error(compiler,
                                  "Unsupported right operand conversion for binary operation.");
                            return;
                        }
                        break;
                    case TYPE_STRING:
                        switch (rightType->kind) {
                            case TYPE_I32:
                                writeOp(compiler, OP_I32_TO_STRING);
                                break;
                            case TYPE_U32:
                                writeOp(compiler, OP_U32_TO_STRING);
                                break;
                            case TYPE_F64:
                                writeOp(compiler, OP_F64_TO_STRING);
                                break;
                            case TYPE_BOOL:
                                writeOp(compiler, OP_BOOL_TO_STRING);
                                break;
                            case TYPE_ARRAY:
                                writeOp(compiler, OP_ARRAY_TO_STRING);
                                break;
                            case TYPE_STRUCT:
                                writeOp(compiler, OP_ARRAY_TO_STRING);
                                break;
                            default:
                                char msgBuffer[256];
                                const char* rightTypeName = getTypeName(rightType->kind);
                                snprintf(msgBuffer, sizeof(msgBuffer),
                                    "Unsupported right operand conversion for binary operation. Right type: '%s', operation at line %d",
                                    rightTypeName, node->data.operation.operator.line);
                                error(compiler, msgBuffer);
                                return;
                        }
                        break;
                    default: {
    const char* leftTypeName = leftType ? getTypeName(leftType->kind) : "(none)";
    const char* rightTypeName = rightType ? getTypeName(rightType->kind) : "(none)";
    char msgBuffer[256];
    snprintf(msgBuffer, sizeof(msgBuffer),
        "unsupported right operand conversion for binary operation: left type '%s', right type '%s', attempted result type '%s'",
        leftTypeName, rightTypeName, getTypeName(resultType));
    char helpBuffer[128];
    snprintf(helpBuffer, sizeof(helpBuffer),
        "try converting the right operand to a compatible type or use explicit string conversion (e.g., str(x))");
    const char* note = "Orus does not support implicit conversion between these types in this operation";
    emitGenericTypeError(compiler, &node->data.operation.operator, msgBuffer, helpBuffer, note);
    return;
                    }
                }
            }


            // Emit the operator instruction
            TokenType operator= node->data.operation.operator.type;

            switch (operator) {
                case TOKEN_PLUS:
                    switch (resultType) {
                        case TYPE_STRING:
                            writeOp(compiler, OP_CONCAT);
                            break;
                        case TYPE_I32:
                            writeOp(compiler, OP_ADD_I32);
                            break;
                        case TYPE_U32:
                            writeOp(compiler, OP_ADD_U32);
                            break;
                        case TYPE_F64:
                            writeOp(compiler, OP_ADD_F64);
                            break;
                        default:
                            error(compiler,
                                  "Addition not supported for this type.");
                            return;
                    }
                    break;

                case TOKEN_MINUS:
                    switch (resultType) {
                        case TYPE_I32:
                            writeOp(compiler, OP_SUBTRACT_I32);
                            break;
                        case TYPE_U32:
                            writeOp(compiler, OP_SUBTRACT_U32);
                            break;
                        case TYPE_F64:
                            writeOp(compiler, OP_SUBTRACT_F64);
                            break;
                        default:
                            error(compiler,
                                  "Subtraction not supported for this type.");
                            return;
                    }
                    break;

                case TOKEN_STAR:
                    switch (resultType) {
                        case TYPE_I32:
                            writeOp(compiler, OP_MULTIPLY_I32);
                            break;
                        case TYPE_U32:
                            writeOp(compiler, OP_MULTIPLY_U32);
                            break;
                        case TYPE_F64:
                            writeOp(compiler, OP_MULTIPLY_F64);
                            break;
                        default:
                            error(
                                compiler,
                                "Multiplication not supported for this type.");
                            return;
                    }
                    break;
                case TOKEN_SLASH:
                    switch (resultType) {
                        case TYPE_I32:
                            writeOp(compiler, OP_DIVIDE_I32);
                            break;
                        case TYPE_U32:
                            writeOp(compiler, OP_DIVIDE_U32);
                            break;
                        case TYPE_F64:
                            writeOp(compiler, OP_DIVIDE_F64);
                            break;
                        default:
                            error(compiler,
                                  "Division not supported for this type.");
                            return;
                    }
                    break;
                case TOKEN_MODULO:
                    switch (resultType) {
                        case TYPE_I32:
                            writeOp(compiler, OP_MODULO_I32);
                            break;
                        case TYPE_U32:
                            writeOp(compiler, OP_MODULO_U32);
                            break;
                        default:
                            error(compiler,
                                  "Modulo not supported for this type.");
                            return;
                    }
                    break;

                case TOKEN_LEFT_BRACKET:
                    writeOp(compiler, OP_ARRAY_GET);
                    break;

                // Comparison operators
                case TOKEN_LESS:
                    switch (leftType->kind) {
                        case TYPE_I32:
                            writeOp(compiler, OP_LESS_I32);
                            break;
                        case TYPE_U32:
                            writeOp(compiler, OP_LESS_U32);
                            break;
                        case TYPE_F64:
                            writeOp(compiler, OP_LESS_F64);
                            break;
                        case TYPE_GENERIC:
                            // Fallback to numeric comparison with conversion
                            writeOp(compiler, OP_LESS_F64);
                            break;
                        default:
                            error(compiler, "Less than not supported for this type.");
                            return;
                    }
                    break;

                case TOKEN_LESS_EQUAL:
                    switch (leftType->kind) {
                        case TYPE_I32:
                            writeOp(compiler, OP_LESS_EQUAL_I32);
                            break;
                        case TYPE_U32:
                            writeOp(compiler, OP_LESS_EQUAL_U32);
                            break;
                        case TYPE_F64:
                            writeOp(compiler, OP_LESS_EQUAL_F64);
                            break;
                        case TYPE_GENERIC:
                            writeOp(compiler, OP_LESS_EQUAL_F64);
                            break;
                        default:
                            error(compiler, "Less than or equal not supported for this type.");
                            return;
                    }
                    break;

                case TOKEN_GREATER:
                    switch (leftType->kind) {
                        case TYPE_I32:
                            writeOp(compiler, OP_GREATER_I32);
                            break;
                        case TYPE_U32:
                            writeOp(compiler, OP_GREATER_U32);
                            break;
                        case TYPE_F64:
                            writeOp(compiler, OP_GREATER_F64);
                            break;
                        case TYPE_GENERIC:
                            writeOp(compiler, OP_GREATER_F64);
                            break;
                        default:
                            error(compiler, "Greater than not supported for this type.");
                            return;
                    }
                    break;

                case TOKEN_GREATER_EQUAL:
                    switch (leftType->kind) {
                        case TYPE_I32:
                            writeOp(compiler, OP_GREATER_EQUAL_I32);
                            break;
                        case TYPE_U32:
                            writeOp(compiler, OP_GREATER_EQUAL_U32);
                            break;
                        case TYPE_F64:
                            writeOp(compiler, OP_GREATER_EQUAL_F64);
                            break;
                        case TYPE_GENERIC:
                            writeOp(compiler, OP_GREATER_EQUAL_F64);
                            break;
                        default:
                            error(compiler, "Greater than or equal not supported for this type.");
                            return;
                    }
                    break;

                case TOKEN_EQUAL_EQUAL:
                    writeOp(compiler, OP_EQUAL);
                    break;

                case TOKEN_BANG_EQUAL:
                    writeOp(compiler, OP_NOT_EQUAL);
                    break;

                // Logical operators
                case TOKEN_AND:
                    writeOp(compiler, OP_AND);
                    break;
                    
                case TOKEN_OR:
                    writeOp(compiler, OP_OR);
                    break;

                default:
                    error(compiler, "Unsupported binary operator.");
                    return;
            }
            break;
        }

        case AST_UNARY: {
            generateCode(compiler, node->left);
            if (compiler->hadError) return;

            TypeKind operandType = node->valueType->kind;
            TokenType operator= node->data.operation.operator.type;

            switch (operator) {
                case TOKEN_MINUS:
                    switch (operandType) {
                        case TYPE_I32:
                            writeOp(compiler, OP_NEGATE_I32);
                            break;
                        case TYPE_U32:
                            writeOp(compiler, OP_NEGATE_U32);
                            break;
                        case TYPE_F64:
                            writeOp(compiler, OP_NEGATE_F64);
                            break;
                        default:
                            error(compiler,
                                  "Negation not supported for this type.");
                            return;
                    }
                    break;
                case TOKEN_NOT:
                    writeOp(compiler, OP_NOT);
                    break;
                default:
                    error(compiler, "Unsupported unary operator.");
                    return;
            }
            break;
        }

        case AST_VARIABLE: {
            writeOp(compiler, OP_GET_GLOBAL);
            writeOp(compiler, node->data.variable.index);
            break;
        }

        case AST_LET: {
            if (node->data.let.initializer) {
                generateCode(compiler,
                             node->data.let.initializer);  // push value
            } else {
                writeOp(compiler, OP_NIL);  // no initializer → nil
            }

            writeOp(compiler, OP_DEFINE_GLOBAL);
            writeByte(compiler, node->data.let.index);  // correct index
            break;
        }

        case AST_PRINT: {
            if (node->data.print.arguments != NULL) {
                // This is a formatted print with interpolation
                
                // 1. Generate code for each argument (in order)
                ASTNode* arg = node->data.print.arguments;
                while (arg != NULL) {
                    generateCode(compiler, arg);
                    if (compiler->hadError) return;
                    arg = arg->next;
                }

                // 2. Then generate code for the format string
                generateCode(compiler, node->data.print.format);
                if (compiler->hadError) return;

                // 3. Push the argument count as constant
                emitConstant(compiler, I32_VAL(node->data.print.argCount));

                // 4. Emit formatted print instruction
                writeOp(compiler, OP_FORMAT_PRINT);
            } else {
                // This is a simple print without interpolation
                generateCode(compiler, node->data.print.format);
                if (compiler->hadError) return;
                writeOp(compiler, OP_PRINT);
            }
            break;
        }

        case AST_ASSIGNMENT: {
            generateCode(compiler, node->left);
            if (compiler->hadError) return;
            writeOp(compiler, OP_SET_GLOBAL);
            writeOp(compiler, node->data.variable.index);
            break;
        }

        case AST_ARRAY_SET: {
            generateCode(compiler, node->right);  // array
            if (compiler->hadError) return;
            generateCode(compiler, node->data.arraySet.index);  // index
            if (compiler->hadError) return;
            generateCode(compiler, node->left);  // value
            if (compiler->hadError) return;
            writeOp(compiler, OP_ARRAY_SET);
            break;
        }

        case AST_SLICE: {
            generateCode(compiler, node->left);
            if (compiler->hadError) return;
            generateCode(compiler, node->data.slice.start);
            if (compiler->hadError) return;
            generateCode(compiler, node->data.slice.end);
            if (compiler->hadError) return;
            writeOp(compiler, OP_SLICE);
            break;
        }

        case AST_FIELD_SET: {
            generateCode(compiler, node->right); // object
            if (compiler->hadError) return;
            emitConstant(compiler, I32_VAL(node->data.fieldSet.index));
            generateCode(compiler, node->left); // value
            if (compiler->hadError) return;
            writeOp(compiler, OP_ARRAY_SET);
            break;
        }

        case AST_ARRAY: {
            int count = 0;
            ASTNode* elem = node->data.array.elements;
            while (elem) {
                generateCode(compiler, elem);
                if (compiler->hadError) return;
                count++;
                elem = elem->next;
            }
            writeOp(compiler, OP_MAKE_ARRAY);
            writeOp(compiler, count);
            break;
        }

        case AST_STRUCT_LITERAL: {
            int count = 0;
            ASTNode* val = node->data.structLiteral.values;
            while (val) {
                generateCode(compiler, val);
                if (compiler->hadError) return;
                count++;
                val = val->next;
            }
            writeOp(compiler, OP_MAKE_ARRAY);
            writeOp(compiler, count);
            break;
        }

        case AST_FIELD: {
            generateCode(compiler, node->left);
            if (compiler->hadError) return;
            emitConstant(compiler, I32_VAL(node->data.field.index));
            writeOp(compiler, OP_ARRAY_GET);
            break;
        }

        case AST_IF: {

            // Generate code for the condition
            generateCode(compiler, node->data.ifStmt.condition);
            if (compiler->hadError) return;

            // Emit a jump-if-false instruction
            // We'll patch this jump later
            int thenJump = compiler->chunk->count;
            writeOp(compiler, OP_JUMP_IF_FALSE);
            writeChunk(compiler->chunk, 0xFF, 0);  // Placeholder for jump offset
            writeChunk(compiler->chunk, 0xFF, 0);  // Placeholder for jump offset

            // Pop the condition value from the stack
            writeOp(compiler, OP_POP);

            // Generate code for the then branch
            generateCode(compiler, node->data.ifStmt.thenBranch);
            if (compiler->hadError) return;

            // Emit a jump instruction to skip the else branch
            // We'll patch this jump later
            int elseJump = compiler->chunk->count;
            writeOp(compiler, OP_JUMP);
            writeChunk(compiler->chunk, 0xFF, 0);  // Placeholder for jump offset
            writeChunk(compiler->chunk, 0xFF, 0);  // Placeholder for jump offset

            // Patch the then jump
            int thenEnd = compiler->chunk->count;
            compiler->chunk->code[thenJump + 1] = (thenEnd - thenJump - 3) >> 8;
            compiler->chunk->code[thenJump + 2] = (thenEnd - thenJump - 3) & 0xFF;

            // Generate code for elif branches if any
            ASTNode* elifCondition = node->data.ifStmt.elifConditions;
            ASTNode* elifBranch = node->data.ifStmt.elifBranches;
            ObjIntArray* elifJumpsObj = NULL;
            int* elifJumps = NULL;
            int elifCount = 0;

            // Count the number of elif branches
            ASTNode* tempCondition = elifCondition;
            while (tempCondition != NULL) {
                elifCount++;
                tempCondition = tempCondition->next;
            }

            // Allocate memory for elif jumps
            if (elifCount > 0) {
                elifJumpsObj = allocateIntArray(elifCount);
                elifJumps = elifJumpsObj->elements;
            }

            // Generate code for each elif branch
            int elifIndex = 0;
            while (elifCondition != NULL && elifBranch != NULL) {
                // Generate code for the elif condition
                generateCode(compiler, elifCondition);
                if (compiler->hadError) {
                    return;
                }

                // Emit a jump-if-false instruction
                // We'll patch this jump later
                int elifThenJump = compiler->chunk->count;
                writeOp(compiler, OP_JUMP_IF_FALSE);
                writeChunk(compiler->chunk, 0xFF, 0);  // Placeholder for jump offset
                writeChunk(compiler->chunk, 0xFF, 0);  // Placeholder for jump offset

                // Pop the condition value from the stack
                writeOp(compiler, OP_POP);

                // Generate code for the elif branch
                generateCode(compiler, elifBranch);
                if (compiler->hadError) {
                    return;
                }

                // Emit a jump instruction to skip the remaining branches
                // We'll patch this jump later
                elifJumps[elifIndex] = compiler->chunk->count;
                writeOp(compiler, OP_JUMP);
                writeChunk(compiler->chunk, 0xFF, 0);  // Placeholder for jump offset
                writeChunk(compiler->chunk, 0xFF, 0);  // Placeholder for jump offset

                // Patch the elif jump
                int elifEnd = compiler->chunk->count;
                compiler->chunk->code[elifThenJump + 1] = (elifEnd - elifThenJump - 3) >> 8;
                compiler->chunk->code[elifThenJump + 2] = (elifEnd - elifThenJump - 3) & 0xFF;

                // Move to the next elif condition and branch
                elifCondition = elifCondition->next;
                elifBranch = elifBranch->next;
                elifIndex++;
            }

            // Generate code for the else branch if it exists
            if (node->data.ifStmt.elseBranch) {
                generateCode(compiler, node->data.ifStmt.elseBranch);
                if (compiler->hadError) {
                    return;
                }
            }

            // Patch the else jump
            int end = compiler->chunk->count;
            compiler->chunk->code[elseJump + 1] = (end - elseJump - 3) >> 8;
            compiler->chunk->code[elseJump + 2] = (end - elseJump - 3) & 0xFF;

            // Patch all elif jumps
            for (int i = 0; i < elifCount; i++) {
                int elifJump = elifJumps[i];
                compiler->chunk->code[elifJump + 1] = (end - elifJump - 3) >> 8;
                compiler->chunk->code[elifJump + 2] = (end - elifJump - 3) & 0xFF;
            }

            (void)elifJumpsObj; // GC-managed

            break;
        }

        case AST_BLOCK: {
            if (node->data.block.scoped) {
                beginScope(compiler);
            }

            // Generate code for each statement in the block
            ASTNode* stmt = node->data.block.statements;
            while (stmt) {
                generateCode(compiler, stmt);
                if (compiler->hadError) {
                    if (node->data.block.scoped) endScope(compiler);
                    return;
                }
                stmt = stmt->next;
            }
            if (node->data.block.scoped) {
                endScope(compiler);
            }
            break;
        }

        case AST_WHILE: {
            // Save the enclosing loop context
            int enclosingLoopStart = compiler->loopStart;
            int enclosingLoopEnd = compiler->loopEnd;
            int enclosingLoopContinue = compiler->loopContinue;
            int enclosingLoopDepth = compiler->loopDepth;

            // Store the current position to jump back to for the loop condition
            compiler->loopStart = compiler->chunk->count;
            compiler->loopDepth++;

            // Generate code for the condition
            generateCode(compiler, node->data.whileStmt.condition);
            if (compiler->hadError) return;

            // Emit a jump-if-false instruction
            // We'll patch this jump later
            int exitJump = compiler->chunk->count;
            writeOp(compiler, OP_JUMP_IF_FALSE);
            writeChunk(compiler->chunk, 0xFF, 0);  // Placeholder for jump offset
            writeChunk(compiler->chunk, 0xFF, 0);  // Placeholder for jump offset

            // Pop the condition value from the stack
            writeOp(compiler, OP_POP);

            // Set the continue position to the start of the loop
            compiler->loopContinue = compiler->loopStart;

            beginScope(compiler);
            // Generate code for the body
            generateCode(compiler, node->data.whileStmt.body);
            if (compiler->hadError) {
                endScope(compiler);
                return;
            }
            endScope(compiler);

            // Emit a loop instruction to jump back to the condition
            writeOp(compiler, OP_LOOP);
            int offset = compiler->chunk->count - compiler->loopStart + 2;
            writeChunk(compiler->chunk, (offset >> 8) & 0xFF, 0);
            writeChunk(compiler->chunk, offset & 0xFF, 0);

            // Patch the exit jump
            int exitDest = compiler->chunk->count;
            compiler->chunk->code[exitJump + 1] = (exitDest - exitJump - 3) >> 8;
            compiler->chunk->code[exitJump + 2] = (exitDest - exitJump - 3) & 0xFF;

            // Set the loop end position
            compiler->loopEnd = exitDest;

            // Patch all break jumps to jump to the current position
            patchBreakJumps(compiler);

            // Restore the enclosing loop context
            compiler->loopStart = enclosingLoopStart;
            compiler->loopEnd = enclosingLoopEnd;
            compiler->loopContinue = enclosingLoopContinue;
            compiler->loopDepth = enclosingLoopDepth;

            break;
        }

        case AST_FOR: {
            emitForLoop(compiler, node);
            break;
        }
        case AST_FUNCTION: {
            beginScope(compiler);
            // Count and collect parameters
            ASTNode* paramList[256];  // Max 256 params
            int paramCount = 0;

            ASTNode* param = node->data.function.parameters;
            while (param != NULL && paramCount < 256) {
                paramList[paramCount++] = param;
                param = param->next;
            }

            // Reserve jump over function body
            int jumpOverFunction = compiler->chunk->count;
            writeOp(compiler, OP_JUMP);
            writeChunk(compiler->chunk, 0xFF, 0);
            writeChunk(compiler->chunk, 0xFF, 0);

            // Record function body start
            int functionStart = compiler->chunk->count;
            // fprintf(stderr, "DEBUG: Function bytecode starts at offset %d\n",
            //         functionStart);

            // Bind parameters to globals
            for (int i = paramCount - 1; i >= 0; i--) {
                writeOp(compiler, OP_SET_GLOBAL);
                writeOp(compiler, paramList[i]->data.let.index);
                // Pop argument after storing
                writeOp(compiler, OP_POP);
            }

            // Emit body and return
            generateCode(compiler, node->data.function.body);
            writeOp(compiler, OP_NIL);
            writeOp(compiler, OP_RETURN);

            // Patch jump over function
            int afterFunction = compiler->chunk->count;
            compiler->chunk->code[jumpOverFunction + 1] =
                (afterFunction - jumpOverFunction - 3) >> 8;
            compiler->chunk->code[jumpOverFunction + 2] =
                (afterFunction - jumpOverFunction - 3) & 0xFF;

            // Create function entry and store its index in the global variable
            if (vm.functionCount >= UINT8_COUNT) {
                error(compiler, "Too many functions defined.");
                return;
            }
            uint8_t funcIndex = vm.functionCount++;
            vm.functions[funcIndex].start = functionStart;
            vm.functions[funcIndex].arity = (uint8_t)paramCount;

            // Store function index in globals for lookup at runtime
            vm.globals[node->data.function.index] = I32_VAL(funcIndex);

            endScope(compiler);
            break;
        }
        case AST_CALL: {
            // Built-in implementations using native registry
            if (node->data.call.nativeIndex != -1) {
                ASTNode* arg = node->data.call.arguments;
                while (arg) {
                    generateCode(compiler, arg);
                    if (compiler->hadError) return;
                    arg = arg->next;
                }
                writeOp(compiler, OP_CALL_NATIVE);
                writeOp(compiler, (uint8_t)node->data.call.nativeIndex);
                writeOp(compiler, (uint8_t)node->data.call.argCount);
                break;
            }

            // Generate code for each argument in source order
            int argCount = 0;
            ASTNode* arg = node->data.call.arguments;

            ASTNode* args[256];
            while (arg != NULL) {
                args[argCount++] = arg;
                arg = arg->next;
            }

            for (int i = 0; i < argCount; i++) {
                generateCode(compiler, args[i]);
                if (compiler->hadError) return;

                if (node->data.call.convertArgs[i]) {
                    /* conversions not implemented */
                }
            }

            writeOp(compiler, OP_CALL);
            writeOp(compiler, node->data.call.index);
            writeOp(compiler, argCount);

            break;
        }

        case AST_RETURN: {
            // Generate code for the return value if present
            if (node->data.returnStmt.value != NULL) {
                generateCode(compiler, node->data.returnStmt.value);
                if (compiler->hadError) return;
            } else {
                // If no return value, return nil
                writeOp(compiler, OP_NIL);
            }

            // Return from the function
            writeOp(compiler, OP_RETURN);

            break;
        }

        case AST_BREAK: {
            if (compiler->loopDepth == 0) {
                error(compiler, "Cannot use 'break' outside of a loop.");
                return;
            }

            int jumpPos = compiler->chunk->count;
            writeOp(compiler, OP_JUMP);
            writeChunk(compiler->chunk, 0xFF, 0);
            writeChunk(compiler->chunk, 0xFF, 0);
            addBreakJump(compiler, jumpPos);
            break;
        }

        case AST_CONTINUE: {
            if (compiler->loopDepth == 0) {
                error(compiler, "Cannot use 'continue' outside of a loop.");
                return;
            }

            bool isForLoop = compiler->loopContinue != compiler->loopStart;

            if (compiler->loopContinue < 0 && isForLoop) {
                // For-loop continue before increment section is emitted.
                int jumpPos = compiler->chunk->count;
                writeOp(compiler, OP_JUMP);
                writeChunk(compiler->chunk, 0xFF, 0);
                writeChunk(compiler->chunk, 0xFF, 0);
                addContinueJump(compiler, jumpPos);
            } else {
                if (!isForLoop) {
                    // While loops need to pop the condition value
                    writeOp(compiler, OP_POP);
                }

                writeOp(compiler, OP_LOOP);
                int offset = compiler->chunk->count - compiler->loopContinue + 2;
                writeChunk(compiler->chunk, (offset >> 8) & 0xFF, 0);
                writeChunk(compiler->chunk, offset & 0xFF, 0);
            }

            break;
        }

        case AST_TRY: {
            beginScope(compiler);
            uint8_t index = node->data.tryStmt.errorIndex;
            int setup = compiler->chunk->count;
            writeOp(compiler, OP_SETUP_EXCEPT);
            writeChunk(compiler->chunk, 0xFF, 0);
            writeChunk(compiler->chunk, 0xFF, 0);
            writeOp(compiler, index);

            generateCode(compiler, node->data.tryStmt.tryBlock);
            if ( compiler->hadError) { endScope(compiler); return; }

            writeOp(compiler, OP_POP_EXCEPT);
            int jumpOver = compiler->chunk->count;
            writeOp(compiler, OP_JUMP);
            writeChunk(compiler->chunk, 0xFF, 0);
            writeChunk(compiler->chunk, 0xFF, 0);

            int handler = compiler->chunk->count;
            compiler->chunk->code[setup + 1] = (handler - setup - 4) >> 8;
            compiler->chunk->code[setup + 2] = (handler - setup - 4) & 0xFF;

            generateCode(compiler, node->data.tryStmt.catchBlock);
            if (compiler->hadError) { endScope(compiler); return; }

            int end = compiler->chunk->count;
            compiler->chunk->code[jumpOver + 1] = (end - jumpOver - 3) >> 8;
            compiler->chunk->code[jumpOver + 2] = (end - jumpOver - 3) & 0xFF;

            endScope(compiler);
            break;
        }

        case AST_IMPORT: {
            // Emit an import instruction with module path constant
            int constant = makeConstant(compiler, node->data.importStmt.path);
            writeOp(compiler, OP_IMPORT);
            writeOp(compiler, (uint8_t)constant);
            break;
        }

        default:
            error(compiler, "Unsupported AST node type in code generator.");
            break;
    }
}

static void emitForLoop(Compiler* compiler, ASTNode* node) {
    beginScope(compiler);
    // Save the enclosing loop context
    int enclosingLoopStart = compiler->loopStart;
    int enclosingLoopEnd = compiler->loopEnd;
    int enclosingLoopContinue = compiler->loopContinue;
    int enclosingLoopDepth = compiler->loopDepth;
    
    // Generate code for the range start expression and store it in the iterator variable
    generateCode(compiler, node->data.forStmt.startExpr);
    if (compiler->hadError) return;

    // Define and initialize the iterator variable
    writeOp(compiler, OP_DEFINE_GLOBAL);
    writeOp(compiler, node->data.forStmt.iteratorIndex);

    // Store the current position to jump back to for the loop condition
    int loopStart = compiler->chunk->count;
    compiler->loopStart = loopStart;
    compiler->loopDepth++;
    
    // Get the iterator value for comparison
    writeOp(compiler, OP_GET_GLOBAL);
    writeOp(compiler, node->data.forStmt.iteratorIndex);
    
    // Get the end value for comparison
    generateCode(compiler, node->data.forStmt.endExpr);
    if (compiler->hadError) return;

    // Compare the iterator with the end value
    Type* iterType = node->data.forStmt.startExpr->valueType;
    if (iterType->kind == TYPE_I32) {
        writeOp(compiler, OP_LESS_I32);
    } else if (iterType->kind == TYPE_U32) {
        writeOp(compiler, OP_LESS_U32);
    } else {
        error(compiler, "Unsupported iterator type for for loop.");
        return;
    }

    // Emit a jump-if-false instruction to exit the loop when condition is false
    int exitJump = compiler->chunk->count;
    writeOp(compiler, OP_JUMP_IF_FALSE);
    writeChunk(compiler->chunk, 0xFF, 0);  // Placeholder for jump offset
    writeChunk(compiler->chunk, 0xFF, 0);  // Placeholder for jump offset

    // Pop the condition value from the stack
    writeOp(compiler, OP_POP);

    // Generate code for the body
    generateCode(compiler, node->data.forStmt.body);
    if (compiler->hadError) return;

    // Store the current position where we're about to emit the increment code
    // This is where continue statements will jump to
    compiler->loopContinue = compiler->chunk->count;
    patchContinueJumps(compiler);

    // After the body, increment the iterator
    // Get the current iterator value
    writeOp(compiler, OP_GET_GLOBAL);
    writeOp(compiler, node->data.forStmt.iteratorIndex);

    // Add the step value
    if (node->data.forStmt.stepExpr) {
        generateCode(compiler, node->data.forStmt.stepExpr);
        if (compiler->hadError) return;
    } else {
        // Default step value is 1
        if (iterType->kind == TYPE_I32) {
            emitConstant(compiler, I32_VAL(1));
        } else if (iterType->kind == TYPE_U32) {
            emitConstant(compiler, U32_VAL(1));
        }
    }

    // Add the step to the iterator
    if (iterType->kind == TYPE_I32) {
        writeOp(compiler, OP_ADD_I32);
    } else if (iterType->kind == TYPE_U32) {
        writeOp(compiler, OP_ADD_U32);
    }

    // Store the incremented value back in the iterator variable
    writeOp(compiler, OP_SET_GLOBAL);
    writeOp(compiler, node->data.forStmt.iteratorIndex);
    
    // Pop the value from the stack after SET_GLOBAL (important for stack cleanliness!)
    writeOp(compiler, OP_POP);

    // Jump back to the condition check
    writeOp(compiler, OP_LOOP);
    int offset = compiler->chunk->count - loopStart + 2;
    writeChunk(compiler->chunk, (offset >> 8) & 0xFF, 0);
    writeChunk(compiler->chunk, offset & 0xFF, 0);

    // Patch the exit jump
    int exitDest = compiler->chunk->count;
    compiler->chunk->code[exitJump + 1] = (exitDest - exitJump - 3) >> 8;
    compiler->chunk->code[exitJump + 2] = (exitDest - exitJump - 3) & 0xFF;
    
    // Set the loop end position to the destination of the exit jump
    compiler->loopEnd = exitDest;
    
    // Patch all break jumps to jump to the current position
    patchBreakJumps(compiler);

    endScope(compiler);

    // Restore the enclosing loop context
    compiler->loopStart = enclosingLoopStart;
    compiler->loopEnd = enclosingLoopEnd;
    compiler->loopContinue = enclosingLoopContinue;
    compiler->loopDepth = enclosingLoopDepth;
}

uint8_t defineVariable(Compiler* compiler, Token name, Type* type) {
    return addLocal(compiler, name, type);
}

uint8_t addLocal(Compiler* compiler, Token name, Type* type) {
    char tempName[name.length + 1];
    memcpy(tempName, name.start, name.length);
    tempName[name.length] = '\0';
    Symbol* existing = findSymbol(&compiler->symbols, tempName);
    if (existing && existing->scope == compiler->scopeDepth) {
        emitRedeclarationError(compiler, &name, tempName);
        return UINT8_MAX;
    }

    if (vm.variableCount >= UINT8_COUNT) {
        error(compiler, "Too many variables.");
        return 0;
    }
    uint8_t index = vm.variableCount++;
    ObjString* nameObj = allocateString(name.start, name.length);
    if (nameObj == NULL) {
        error(compiler, "Memory allocation failed for variable name.");
        return 0;
    }
    vm.variableNames[index].name = nameObj;

    vm.variableNames[index].length = name.length;
    variableTypes[index] = type;  // Should be getPrimitiveType result
    vm.globalTypes[index] = type;
    vm.globals[index] = NIL_VAL;

    addSymbol(&compiler->symbols, nameObj->chars, name, type, compiler->scopeDepth, index);

    return index;
}

uint8_t resolveVariable(Compiler* compiler, Token name) {
    char tempName[name.length + 1];
    memcpy(tempName, name.start, name.length);
    tempName[name.length] = '\0';
    Symbol* sym = findSymbol(&compiler->symbols, tempName);
    if (sym) return sym->index;
    return UINT8_MAX;  // Not found
}

// Add a break jump to the array
static void addBreakJump(Compiler* compiler, int jumpPos) {
    if (compiler->breakJumps == NULL) {
        compiler->breakJumpCapacity = 8;
        compiler->breakJumps = allocateIntArray(compiler->breakJumpCapacity);
    } else if (compiler->breakJumpCount >= compiler->breakJumpCapacity) {
        int oldCapacity = compiler->breakJumpCapacity;
        compiler->breakJumpCapacity = oldCapacity * 2;
        compiler->breakJumps->elements =
            realloc(compiler->breakJumps->elements,
                    sizeof(int) * compiler->breakJumpCapacity);
        compiler->breakJumps->length = compiler->breakJumpCapacity;
    }
    compiler->breakJumps->elements[compiler->breakJumpCount++] = jumpPos;
}

// Add a continue jump to the array
static void addContinueJump(Compiler* compiler, int jumpPos) {
    if (compiler->continueJumps == NULL) {
        compiler->continueJumpCapacity = 8;
        compiler->continueJumps = allocateIntArray(compiler->continueJumpCapacity);
    } else if (compiler->continueJumpCount >= compiler->continueJumpCapacity) {
        int oldCapacity = compiler->continueJumpCapacity;
        compiler->continueJumpCapacity = oldCapacity * 2;
        compiler->continueJumps->elements =
            realloc(compiler->continueJumps->elements,
                    sizeof(int) * compiler->continueJumpCapacity);
        compiler->continueJumps->length = compiler->continueJumpCapacity;
    }
    compiler->continueJumps->elements[compiler->continueJumpCount++] = jumpPos;
}

// Patch all continue jumps to jump to the loopContinue position
static void patchContinueJumps(Compiler* compiler) {
    int continueDest = compiler->loopContinue;
    for (int i = 0; i < compiler->continueJumpCount; i++) {
        int jumpPos = compiler->continueJumps->elements[i];
        int offset = continueDest - jumpPos - 3;
        compiler->chunk->code[jumpPos + 1] = (offset >> 8) & 0xFF;
        compiler->chunk->code[jumpPos + 2] = offset & 0xFF;
    }
    compiler->continueJumpCount = 0;
}

// Patch all break jumps to jump to the current position
static void patchBreakJumps(Compiler* compiler) {
    int breakDest = compiler->chunk->count;

    // Patch all break jumps to jump to the current position
    for (int i = 0; i < compiler->breakJumpCount; i++) {
        int jumpPos = compiler->breakJumps->elements[i];
        int offset = breakDest - jumpPos - 3;
        compiler->chunk->code[jumpPos + 1] = (offset >> 8) & 0xFF;
        compiler->chunk->code[jumpPos + 2] = offset & 0xFF;
    }

    // Reset the break jumps array
    compiler->breakJumpCount = 0;
}

// Perform a prepass over the AST to record all function declarations so
// they can be referenced before their definitions.
static void predeclareFunction(Compiler* compiler, ASTNode* node) {
    char tempName[node->data.function.name.length + 1];
    memcpy(tempName, node->data.function.name.start, node->data.function.name.length);
    tempName[node->data.function.name.length] = '\0';
    Symbol* existing = findSymbol(&compiler->symbols, tempName);
    uint8_t index;
    if (existing && existing->scope == compiler->scopeDepth && node->data.function.implType) {
        const char* structName = node->data.function.implType->info.structure.name->chars;
        size_t structLen = strlen(structName);
        size_t funcLen = node->data.function.name.length;
        char* temp = (char*)malloc(structLen + 1 + funcLen + 1);
        memcpy(temp, structName, structLen);
        temp[structLen] = '_';
        memcpy(temp + structLen + 1, node->data.function.name.start, funcLen);
        temp[structLen + 1 + funcLen] = '\0';

        ObjString* fullStr = allocateString(temp, structLen + 1 + funcLen);
        free(temp);

        Token newTok = node->data.function.name;
        newTok.start = fullStr->chars;
        newTok.length = structLen + 1 + funcLen;
        node->data.function.name = newTok;
        node->data.function.mangledName = fullStr;
        index = defineVariable(compiler, newTok, node->data.function.returnType);
    } else {
        index = defineVariable(compiler, node->data.function.name, node->data.function.returnType);
    }
    node->data.function.index = index;
    vm.functionDecls[index] = node;

    int pcount = 0;
    ASTNode* p = node->data.function.parameters;
    while (p) { pcount++; p = p->next; }
    Type** paramTypes = NULL;
    if (pcount > 0) {
        paramTypes = (Type**)malloc(sizeof(Type*) * pcount);
        p = node->data.function.parameters;
        for (int i = 0; i < pcount; i++) {
            paramTypes[i] = p->data.let.type;
            p = p->next;
        }
    }
    Type* funcType = createFunctionType(node->data.function.returnType,
                                       paramTypes, pcount);
    variableTypes[index] = funcType;
    vm.globalTypes[index] = funcType;
}

static void recordFunctionDeclarations(ASTNode* ast, Compiler* compiler) {
    ASTNode* current = ast;
    while (current) {
        if (current->type == AST_FUNCTION) {
            predeclareFunction(compiler, current);
        } else if (current->type == AST_BLOCK && !current->data.block.scoped) {
            recordFunctionDeclarations(current->data.block.statements, compiler);
        }
        current = current->next;
    }
}

void initCompiler(Compiler* compiler, Chunk* chunk,
                  const char* filePath, const char* sourceCode) {
    compiler->loopStart = -1;
    compiler->loopEnd = -1;
    compiler->loopContinue = -1;
    compiler->loopDepth = 0;

    // Initialize break jumps array
    compiler->breakJumps = NULL;
    compiler->breakJumpCount = 0;
    compiler->breakJumpCapacity = 0;

    // Initialize continue jumps array
    compiler->continueJumps = NULL;
    compiler->continueJumpCount = 0;
    compiler->continueJumpCapacity = 0;

    initSymbolTable(&compiler->symbols);
    compiler->scopeDepth = 0;
    compiler->chunk = chunk;
    compiler->hadError = false;
    compiler->panicMode = false;

    compiler->filePath = filePath;
    compiler->sourceCode = sourceCode;

    // Count lines in sourceCode and record start pointers for each line
    if (sourceCode) {
        int lines = 1;
        const char* p = sourceCode;
        while (*p) {
            if (*p == '\n') lines++;
            p++;
        }
        compiler->lineCount = lines;
        compiler->lineStarts = malloc(sizeof(const char*) * lines);
        compiler->lineStarts[0] = sourceCode;
        p = sourceCode;
        int line = 1;
        while (*p && line < lines) {
            if (*p == '\n') compiler->lineStarts[line++] = p + 1;
            p++;
        }
    } else {
        compiler->lineStarts = NULL;
        compiler->lineCount = 0;
    }
}

// Free resources used by the compiler
static void freeCompiler(Compiler* compiler) {
    // Allow GC to reclaim jump arrays
    compiler->breakJumps = NULL;
    compiler->breakJumpCount = 0;
    compiler->breakJumpCapacity = 0;

    compiler->continueJumps = NULL;
    compiler->continueJumpCount = 0;
    compiler->continueJumpCapacity = 0;

    freeSymbolTable(&compiler->symbols);

    if (compiler->lineStarts) {
        free((void*)compiler->lineStarts);
        compiler->lineStarts = NULL;
    }
}

bool compile(ASTNode* ast, Compiler* compiler, bool requireMain) {
    initTypeSystem();
    recordFunctionDeclarations(ast, compiler);
    ASTNode* current = ast;
    // Removed unused index variable
    while (current) {
        typeCheckNode(compiler, current);
        if (!compiler->hadError) {
            generateCode(compiler, current);
        }
        current = current->next;
    }

    // Automatically invoke `main` if it exists or report an error
    Token mainTok;
    mainTok.type = TOKEN_IDENTIFIER;
    mainTok.start = "main";
    mainTok.length = 4;
    mainTok.line = 0;
    uint8_t mainIndex = resolveVariable(compiler, mainTok);

    if (mainIndex != UINT8_MAX) {
        writeOp(compiler, OP_CALL);
        writeOp(compiler, mainIndex);
        writeOp(compiler, 0); // no arguments
        writeOp(compiler, OP_POP); // discard return value
    } else if (requireMain) {
        error(compiler, "No 'main' function defined.");
    }

    writeOp(compiler, OP_RETURN);
    
    if (vm.trace) {
#ifdef DEBUG_TRACE_EXECUTION
        disassembleChunk(compiler->chunk, "code");
#endif
    }
    
    freeCompiler(compiler);
    return !compiler->hadError;
}
