#ifndef COMPILER_H
#define COMPILER_H

#include "ast.h"
#include "chunk.h"
#include "symtable.h"
#include "type.h"

typedef struct {
    int loopStart;         // Start position of the current loop
    int loopEnd;           // End position of the current loop (for breaks)
    int loopContinue;      // Position to jump to for continue statements
    int loopDepth;         // Nesting level of loops

    // Arrays to store break and continue jumps for patching
    int* breakJumps;       // Array of positions where break statements jump from
    int breakJumpCount;    // Number of break jumps
    int breakJumpCapacity; // Capacity of the breakJumps array

    SymbolTable* symbols;
    Chunk* chunk;
    bool hadError;
    bool panicMode;
} Compiler;

void initCompiler(Compiler* compiler, Chunk* chunk);
bool compile(ASTNode* ast, Compiler* compiler);
uint8_t resolveVariable(Compiler* compiler, Token name);       // Added
uint8_t addLocal(Compiler* compiler, Token name, Type* type);  // Added
uint8_t defineVariable(Compiler* compiler, Token name, Type* type);  // Added

#endif