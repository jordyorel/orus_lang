# Roadmap for Enabling Effective `use` Imports in Orus (C-based Language)

This roadmap outlines the detailed steps to make the `use` import system in Orus functional. 
---

## ✅ Goals

* Support `use math`, `use datetime as dt` style imports.
* Modules are imported as a whole and referenced through the module name.
* Ensure imported files execute once and expose usable functions, types, and constants.
* Maintain a clean, professional structure aligned with the current codebase.

---

## 🗂️ Where to Implement

| Feature                    | File(s) to Modify                         |
| -------------------------- | ----------------------------------------- |
| Import resolution          | `src/compiler/compiler.c`                 |
| Module file loading        | `src/util/file_utils.c`                   |
| AST representation         | `src/compiler/ast.c`, `include/ast.h`     |
| Parsing new `use` syntax   | `src/parser/parser.c`, `include/parser.h` |
| Symbol definition          | `src/compiler/symtable.c`                 |
| Runtime execution          | `src/vm/vm.c`                             |
| Value handling for modules | `src/vm/value.c`, `include/value.h`       |

---

## 🔧 Function Signature Proposals

### 1. Load Orus file from path

```c
char* load_module_source(const char* resolved_path);
```

### 2. Parse a source string into an AST

```c
ASTNode* parse_module_source(const char* source_code, const char* module_name);
```

### 3. Compile module AST into bytecode

```c
Chunk* compile_module_ast(ASTNode* ast, const char* module_name);
```

### 4. Cache compiled modules globally

```c
typedef struct {
    char* module_name;
    Chunk* bytecode;
    Table exports; // exported functions/types/constants
} Module;

bool register_module(Module*);
Module* get_module(const char* name);
```

---

## 🧩 Step-by-Step Roadmap

### Step 1: Parse `use` Statements ✅

* Extend `parser.c` to recognize:

  ```orus
  use math
  use datetime as dt
  use tests::modules::hello_module
  use tests::modules::hello_module as hm
  ```
* Output an `ImportNode` in AST with:

  * full module path (`tests/modules/hello_module.orus`)
  * optional alias name
  * optional list of selected symbols

### Step 2: Resolve Module Path ✅

* In `compiler.c`, convert `use tests::modules::hello_module` to:

  ```c
  tests/modules/hello_module.orus
  ```
* Use the path to locate the module file on disk

### Step 3: Load and Parse Module ✅

* Use `file_utils.c` to load file contents.
* Pass to `parser` → AST → `compiler` → bytecode (like normal program).
* Store result in a global module registry.

### Step 4: Execute Module Once ✅

* Use `get_module()` to check if already loaded.
* If the module has already executed, report an error instead of running it again.
* If not, compile and run it in an isolated scope.
* Store public functions/values into an `exports` map.

### Step 5: Bind Imports to Symbol Table ✅

* When compiling the main file, register the module under its name or alias.
* Access all public members through that module name.

### Step 6: Handle Aliasing

* `use datetime as dt` should alias the module in symbol table.
* `use tests::modules::hello_module as hm` binds all public members under `hm`
* Access becomes `hm.greet()`

### Step 7: Prevent Recompilation ✅

* Register compiled modules in a global cache.
* On re-import, retrieve from cache instead of reloading/recompiling.


---

## 🛡️ Error Handling

* Undefined module → "Module `foo` not found"
* Missing export → "Symbol `bar` not found in module `foo`"
* Import cycle → detect and prevent infinite recursion

---

## ✅ Example Flow: `use math`

1. Parser reads and stores the `use` statement
2. Compiler resolves the file path
3. File content is read
4. Parsed into AST
5. Compiled to bytecode
6. Public symbols are registered in the module export table
7. The module is bound under the name `math`
8. Later calls use `math.clamp(...)`

---

## 📌 Enhancements

The import system now supports:

* The `pub` keyword to mark exported functions in modules.
* `use *` syntax to import all public members of a module.
* Accessing loaded module metadata via `module_name()` and `module_path()`.
* A `--trace-imports` CLI flag for debugging module loading.

---
