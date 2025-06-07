# Orus Language Reference

This document provides a comprehensive reference for the Orus programming language (version 0.1.0).
All examples are taken from the programs located in the `tests/` directory.

## Primitive Types

Orus supports the following built-in primitive types:

- `i32` – Signed 32-bit integers (range: -2,147,483,648 to 2,147,483,647)
- `u32` – Unsigned 32-bit integers (range: 0 to 4,294,967,295)
- `f64` – 64-bit IEEE 754 floating point numbers (double precision)
- `bool` – Boolean values, represented as either `true` or `false`
- `string` – UTF-8 encoded text strings
- `nil` – Absence of a value, automatically returned from functions without an explicit return statement

Examples:
```orus
let signed_int: i32 = -42
let unsigned_int: u32 = 100
let float_num: f64 = 3.14159
let boolean: bool = true
let text: string = "Hello, Orus"
```

## Compound Types

Orus provides two primary compound data types:

### Arrays

Arrays are fixed-length collections declared with the syntax `[ElementType; Size]`. Arrays are zero-indexed and can be accessed using square bracket notation.

Declaration and initialization:
```orus
// Declare an array of 5 integers
let numbers: [i32; 5] = [1, 2, 3, 4, 5]

// Access array elements (zero-indexed)
let first = numbers[0]  // 1
let third = numbers[2]  // 3

// Modify array elements
numbers[1] = 20

// Multidimensional arrays
let matrix: [i32; 2][2] = [[1, 2], [3, 4]]
let value = matrix[0][1]  // 2
```

### Dynamic Arrays

While arrays have a fixed declared size, they can grow dynamically when used with these built-in functions:

- `push(array, element)` – Appends an element to the end of an array, automatically expanding capacity
- `pop(array)` – Removes and returns the last element of an array
- `len(array)` – Returns the current length of an array

Example:
```orus
let numbers: [i32; 1] = [0]  // Initial capacity of 1
push(numbers, 10)            // Array grows to size 2
push(numbers, 20)            // Array grows to size 3
print(len(numbers))          // Prints 3
let last = pop(numbers)      // last = 20, array size back to 2
```

### Structs

Structs are user-defined record types with named fields. They are defined using the `struct` keyword.

Definition and instantiation:
```orus
// Define a struct
struct Point {
    x: i32,
    y: i32
}

// Instantiate a struct
let p1 = Point{x: 10, y: 20}

// Access struct fields
let x_value = p1.x
```

## Variables

Variables are introduced with the `let` keyword and follow these rules:

- All variables must be explicitly declared before use
- Type annotations are optional when the type can be inferred
- Variables can be reassigned with a compatible value
- Variable scope is block-based
- Variables cannot be declared outside functions
- Variable names follow the common identifier rules (letters, digits, underscore; must start with letter/underscore)

Examples:
```orus
let count = 0                 // Type inference (i32)
let text: string = "hello"    // Explicit type annotation
let flag = true               // Type inference (bool)

// Reassignment 
count = 10                    // Simple reassignment

// Block scope
{
    let local = 5             // Only visible in this block
}
// local is not accessible here
```

## Operators

Orus provides these operators with standard precedence rules:

### Arithmetic Operators
- `+` – Addition (numbers) or concatenation (strings)
- `-` – Subtraction
- `*` – Multiplication
- `/` – Division (integer division for i32/u32, floating point division for f64)
- `%` – Modulo (remainder after division)

### Comparison Operators
- `==` – Equal to
- `!=` – Not equal to
- `<` – Less than
- `>` – Greater than
- `<=` – Less than or equal to
- `>=` – Greater than or equal to

### Logical Operators
- `and` – Logical AND
- `or` – Logical OR
- `not` – Logical NOT (unary)

### Type Conversion

Type conversion must be performed explicitly, as Orus does not perform implicit type conversions between numeric types.

## Modules and Imports

Orus organizes code in files that serve as modules. The module system follows these rules:

- Files can be imported using the `import` statement with a string literal path
- Import statements must appear at the top level of a file, not inside functions
- Each file is executed only once during the program's lifetime, regardless of how many times it's imported
- Modules can contain function definitions, struct definitions, and `impl` blocks

Example:
```orus
import "path/to/module.orus"  // Must appear at top level

fn main() {
    // Call functions from the imported module
    module_function()
}
```

### Program Entry Point

All Orus programs must define a `main` function, which serves as the entry point:

```orus
fn main() {
    // Program execution starts here
    print("Hello, world!")
}
```

Requirements:
- The `main` function must be defined (directly or via imports)
- Top-level code outside functions is not allowed except for imports and struct/impl definitions
- `let` declarations and statements must be inside functions

## Functions

Functions are defined with the `fn` keyword and follow these rules:

- Parameter types must be explicitly declared
- Return type is specified with the `->` syntax
- If a return type is declared, all code paths must return a value of that type
- Functions without a return type declaration implicitly return `nil`
- Parameters are passed by value
- Functions may be called before their definitions appear

Examples:
```orus
// Function with parameters and return value
fn add(a: i32, b: i32) -> i32 {
    return a + b
}

// Function with multiple return paths
fn max(a: i32, b: i32) -> i32 {
    if a > b {
        return a
    }
    return b
}

// Function with no explicit return (returns nil)
fn greet(name: string) {
    print("Hello, {}!", name)
}

// Recursive function
fn factorial(n: i32) -> i32 {
    if n <= 1 {
        return 1
    }
    return n * factorial(n - 1)
}
```

## Control Flow

Orus provides the following control flow constructs:

### Conditionals

```orus
// Simple if
if condition {
    // code executed if condition is true
}

// If-else
if condition {
    // code executed if condition is true
} else {
    // code executed if condition is false
}

// If-elif-else chain
if condition1 {
    // code for condition1
} elif condition2 {
    // code for condition2
} elif condition3 {
    // code for condition3
} else {
    // default case
}
```

### Loops

```orus
// For loop with range
for i in 0..10 {       // Range is inclusive of start, exclusive of end (0 to 9)
    print(i)
}

// While loop
while condition {
    // code executed as long as condition is true
}
```

### Loop Control

```orus
// Break statement (exits the loop)
while true {
    if condition {
        break           // Exits the loop immediately
    }
}

// Continue statement (skips to next iteration)
for i in 0..10 {
    if i % 2 == 0 {
        continue        // Skip even numbers, continue with next iteration
    }
    print(i)            // Only prints odd numbers
}
```

## Methods with `impl`

Methods are defined inside `impl` blocks attached to a struct type:

```orus
struct Rectangle {
    width: i32,
    height: i32
}

impl Rectangle {
    // Instance method (requires an instance of Rectangle)
    fn area(self) -> i32 {
        return self.width * self.height
    }
    
    // Static method (creates and returns a new Rectangle)
    fn new(w: i32, h: i32) -> Rectangle {
        return Rectangle{
            width: w,
            height: h
        }
    }
}
```

Usage:
```orus
fn main() {
    // Call static method
    let rect = Rectangle.new(5, 10)
    
    // Call instance method
    let a = rect.area()  // Returns 50
}
```

Key points:
- Instance methods receive `self` as their first parameter
- Static methods are called with the struct name followed by a dot
- Instance methods are called on instances of the struct
- Multiple `impl` blocks can be defined for the same struct

## Printing and String Formatting

Orus provides a built-in `print` function for console output:

```orus
// Simple printing
print("Hello, world!")

// String interpolation with placeholders
let name = "Alice"
let age = 30
print("{} is {} years old", name, age)  // Alice is 30 years old

// Print expressions
print("The result is: {}", 10 * 5 + 2)
```

String interpolation features:
- Each `{}` placeholder is replaced with the corresponding argument
- Arguments are converted to strings automatically
- The number of placeholders should match the number of additional arguments

## String Operations

Orus supports the following string operations:

```orus
// String concatenation with +
let greeting = "Hello, " + "world!"

// String length
let length = len("Hello")  // 5

// Substring extraction: substring(str, start, end)
let part = substring("Hello, world!", 0, 5)  // "Hello"
```

## Error Handling

Orus provides exception-like error handling with `try`/`catch` blocks:

```orus
try {
    // Code that might cause an error
    let result = 10 / 0  // Division by zero error
} catch err {
    // Error handling code
    print("Error occurred: {}", err)
}
```

Error types:
- Runtime errors (e.g., division by zero)
- Type errors (e.g., incompatible types in an operation)
- I/O errors (e.g., failed file operations)

Error messages include the location of the failure using the format
`file:line:column: message`. When an error unwinds through function calls,
a short stack trace is printed showing the call chain.

## Generics

Orus functions and structs can take generic type parameters. Generic parameters
are declared after the name using angle brackets and can be referenced within
the definition. Type arguments may be supplied at call sites.

```orus
fn id<T>(x: T) -> T {
    return x
}

struct Box<T> {
    value: T,
}

fn main() {
    print(id<i32>(1))
    print(id<string>("hi"))
    let b: Box<i32> = Box { value: 2 }
    print(b.value)
}
```

Generic parameters are checked during compilation and must be supplied or can
be inferred from argument types. The compiler verifies that generic arguments
match usage within the function or struct.

