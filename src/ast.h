#ifndef clox_ast_h
#define clox_ast_h

#include "common.h"
#include "scanner.h"
#include "type.h"
#include "value.h"

typedef enum {
    AST_LITERAL,
    AST_BINARY,
    AST_UNARY,
    AST_VARIABLE,
    AST_ASSIGNMENT,
    AST_CALL,
    AST_LET,
    AST_PRINT,
    AST_IF,
    AST_BLOCK,
    AST_WHILE,
    AST_FOR,
    AST_FUNCTION,
    AST_RETURN,
    AST_BREAK,
    AST_CONTINUE
} ASTNodeType;

typedef struct {
    Token name;
    uint8_t index;
} VariableData;

typedef struct {
    Token name;
    Type* type;
    struct ASTNode* initializer;
    uint8_t index;
} LetData;

typedef struct {
    struct ASTNode* format;     // Format string expression
    struct ASTNode* arguments;  // Linked list of argument expressions
    int argCount;               // Number of arguments
} PrintData;

typedef struct {
    struct ASTNode* condition;
    struct ASTNode* thenBranch;
    struct ASTNode* elifConditions;  // Linked list of elif conditions
    struct ASTNode* elifBranches;    // Linked list of elif branches
    struct ASTNode* elseBranch;
} IfData;

typedef struct {
    struct ASTNode* statements;  // Linked list of statements
} BlockData;

typedef struct {
    struct ASTNode* condition;  // Loop condition
    struct ASTNode* body;       // Loop body
} WhileData;

typedef struct {
    Token iteratorName;         // Iterator variable name
    uint8_t iteratorIndex;      // Iterator variable index
    struct ASTNode* startExpr;  // Start of range
    struct ASTNode* endExpr;    // End of range
    struct ASTNode* stepExpr;   // Step value (optional)
    struct ASTNode* body;       // Loop body
} ForData;

typedef struct {
    Token name;                // Function name
    struct ASTNode* parameters; // Linked list of parameter nodes
    Type* returnType;          // Return type
    struct ASTNode* body;      // Function body
    uint8_t index;             // Function index in the function table
} FunctionData;

typedef struct {
    Token name;               // Function name
    struct ASTNode* arguments; // Linked list of argument nodes
    uint8_t index;            // Function index in the function table
    bool* convertArgs;         // Array of flags for argument conversion
    int argCount;             // Number of arguments
} CallData;

typedef struct {
    struct ASTNode* value;    // Return value expression
} ReturnData;

typedef struct ASTNode {
    ASTNodeType type;
    struct ASTNode* left;
    struct ASTNode* right;
    struct ASTNode* next;
    union {
        Value literal;
        struct {
            Token operator;
            int arity;
            bool convertLeft;   // Flag to indicate if left operand needs conversion
            bool convertRight;  // Flag to indicate if right operand needs conversion
        } operation;
        VariableData variable;
        LetData let;
        PrintData print;
        IfData ifStmt;
        BlockData block;
        WhileData whileStmt;
        ForData forStmt;
        FunctionData function;
        CallData call;
        ReturnData returnStmt;
    } data;
    Type* valueType;
} ASTNode;

ASTNode* createLiteralNode(Value value);
ASTNode* createBinaryNode(Token operator, ASTNode * left, ASTNode* right);
ASTNode* createUnaryNode(Token operator, ASTNode * operand);
ASTNode* createVariableNode(Token name, uint8_t index);
ASTNode* createLetNode(Token name, Type* type, ASTNode* initializer);
ASTNode* createPrintNode(ASTNode* format, ASTNode* arguments, int argCount);
ASTNode* createAssignmentNode(Token name, ASTNode* value);
ASTNode* createIfNode(ASTNode* condition, ASTNode* thenBranch, ASTNode* elifConditions, ASTNode* elifBranches, ASTNode* elseBranch);
ASTNode* createBlockNode(ASTNode* statements);
ASTNode* createWhileNode(ASTNode* condition, ASTNode* body);
ASTNode* createForNode(Token iteratorName, ASTNode* startExpr, ASTNode* endExpr, ASTNode* stepExpr, ASTNode* body);
ASTNode* createFunctionNode(Token name, ASTNode* parameters, Type* returnType, ASTNode* body);
ASTNode* createCallNode(Token name, ASTNode* arguments, int argCount);
ASTNode* createReturnNode(ASTNode* value);
ASTNode* createBreakNode();
ASTNode* createContinueNode();

void freeASTNode(ASTNode* node);

#endif