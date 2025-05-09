#ifndef clox_scanner_h
#define clox_scanner_h

typedef enum {
  // Single-character tokens.
  TOKEN_LEFT_PAREN, TOKEN_RIGHT_PAREN,
  TOKEN_LEFT_BRACE, TOKEN_RIGHT_BRACE,
  TOKEN_COMMA, TOKEN_DOT, TOKEN_MINUS, TOKEN_PLUS,
  TOKEN_SEMICOLON, TOKEN_SLASH, TOKEN_STAR,
  // One or two character tokens.
  TOKEN_BANG, TOKEN_BANG_EQUAL,
  TOKEN_EQUAL, TOKEN_EQUAL_EQUAL,
  TOKEN_GREATER, TOKEN_GREATER_EQUAL,
  TOKEN_LESS, TOKEN_LESS_EQUAL, TOKEN_MODULO,
  TOKEN_DOT_DOT, // Range operator

  // function return
  TOKEN_ARROW,

  // Literals.
  TOKEN_IDENTIFIER, TOKEN_STRING, TOKEN_NUMBER,
  // Keywords.
  TOKEN_AND, TOKEN_BREAK, TOKEN_CLASS, TOKEN_CONTINUE, TOKEN_ELSE, TOKEN_ELIF, TOKEN_FALSE,
  TOKEN_FOR, TOKEN_FN, TOKEN_IF, TOKEN_NIL, TOKEN_OR,
  TOKEN_PRINT, TOKEN_RETURN, TOKEN_SUPER, TOKEN_THIS,
  TOKEN_TRUE, TOKEN_LET, TOKEN_WHILE, TOKEN_INT, TOKEN_IN, TOKEN_BOOL,

  // Add type tokens
  TOKEN_U32,  // Add this
  TOKEN_F64,  // Add this

  TOKEN_ERROR, TOKEN_EOF,

  TOKEN_NEWLINE,

  TOKEN_COLON,      // Add this for type annotations
} TokenType;

typedef struct {
    TokenType type;
    const char* start;
    int length;
    int line;
} Token;

typedef struct {
    const char* start;
    const char* current;
    int line;
} Scanner;

typedef struct {
    const char* keyword;
    TokenType type;
} KeywordEntry;

void init_scanner(const char* source);
Token scan_token();


#endif