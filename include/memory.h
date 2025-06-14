#ifndef clox_memory_h
#define clox_memory_h

#include "common.h"
#include "value.h"
#include "error.h"


// This macro is used to grow the capacity of the dynamic array that stores the
// bytecode instructions. It ensures that the capacity is at least 8, and doubles it otherwise
#define GROW_CAPACITY(capacity) \
    ((capacity) < 8 ? 8 : (capacity) * 2)

// static inline size_t growCapacity(size_t capacity) {
//     if (capacity < 8) {
//         return 8;
//     } else {
//         return capacity * 2;
//     }
// }

// This macro is used to grow the size of a dynamic array. It takes the type of
// the array, the pointer to the array, the old count of elements, and the new
#define GROW_ARRAY(type, pointer, oldCount, newCount)     \
    (type*)reallocate(pointer, sizeof(type) * (oldCount), \
                      sizeof(type) * (newCount))

// This macro can aloso be implemented as a function:
// static inline size_t growArray(size_t oldCount, size_t newCount) {
//     return oldCount < 8 ? 8 : oldCount * 2;
// }

#define GROW_STACK(vm, oldCapacity, newCapacity) \
    ((vm)->stack = GROW_ARRAY(Value, (vm)->stack, oldCapacity, newCapacity))

#define GROW_STACK_IF_NEEDED(vm)                                       \
    if ((vm)->stackTop - (vm)->stack >= (vm)->stackCapacity) {         \
        int oldCapacity = (vm)->stackCapacity;                         \
        (vm)->stackCapacity = GROW_CAPACITY(oldCapacity);              \
        GROW_STACK(vm, oldCapacity, (vm)->stackCapacity);              \
        if (!(vm)->stack) {                                            \
            fprintf(stderr, "Failed to allocate memory for stack!\n"); \
            exit(1);                                                   \
        }                                                              \
        (vm)->stackTop = (vm)->stack + oldCapacity;                    \
    }

// static inline size_t growArray(type, pointer, oldCount, newCount) {
//     return reallocate(pointer, sizeof(type) * (oldCount), sizeof(type) * (newCount));
// }

// This macro is used to free the memory associated with a dynamic array. It
// takes the type of the array, the pointer to the array, and the old count of
// elements
#define FREE_ARRAY(type, pointer, oldCount)\
    (type*)reallocate(pointer, sizeof(type) * (oldCount), 0)

// Allocates memory for a new object of a given type. It takes the type of the
void* reallocate(void* pointer, size_t oldSize, size_t newSize);


// Allocate a new string object copying the given characters
ObjString* allocateString(const char* str, int length);

// Allocate a new array object with the given length
ObjArray* allocateArray(int length);
ObjIntArray* allocateIntArray(int length);
struct ObjError* allocateError(ErrorType type, const char* message, SrcLocation location);

// Allocate AST and Type objects
struct ASTNode* allocateASTNode();
struct Type* allocateType();

// Mark helpers for GC
void markObject(Obj* object);
void markValue(Value value);

// Garbage collector interface
void collectGarbage();
void freeObjects();

// Utility to copy a raw C string onto the heap
char* copyString(const char* str, int length);

#endif
