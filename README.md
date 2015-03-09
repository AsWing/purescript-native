**Pure11** is an experimental C++11 compiler/backend for [PureScript](https://github.com/purescript/purescript). It attempts to generate "sane" and performant C++11 code (instead of JavaScript), in the spirit of PureScript.

#### Status:

* Alpha (0.1) — very early, contributions welcome!

#### Performance

* No runtime system (beyond the standard C++11 runtime library)
* Uses template metaprogramming extensively to translate the original source type information — minimal performance cost when running
* Uses native C++11 reference counting (`std::shared_ptr`) for relatively lightweight automatic memory management
* Uses PureScript's normal tail call optimizations for generated C++11 code

#### Differences from PureScript:

* Inline code (foreign imports) are C++11 instead of JavaScript
* Built in `Int` (C++ `int`), `Integer` (C++ `long long`), Char (C++ `char`) primitive types
* Compiler is `pcc` instead of `psc` or `psc-make`, and only supports `make` mode
  - Generates a simple CMake file for easy experimentation
* No Pure11-specific REPL right now

#### Other notes:

* Built-in lists use a custom, STL-like `shared_list` (immutable list) type
  - Built-in conversions to `std::vector`
  - Built-in conversions to `std::string` for `Char` list
* `String` type corresponds to `std::string` (at least for now)
* `Number` is C++ `double` type, with `Double` and `Float` aliases

#### TO-DO:

* Proper break-out of pure11 generation — just a hacked fork right now
* Get automated builds/tests up and running (equivalents of PureScript)
* Support for `type` in generator (e.g. generate C++11 `using`)
* Introduce `Char` literals (make similar to Haskell's), possibly try to push upstream to PureScript
* Optimized `newtype` (some work already done, but disabled for now)
* ST monad (in Prelude)
* "Magic do" (similar work already done in inliner and TCO code)
* Unicode (UTF-8) support for `String` (use code from my Idris backend)
* Lots of testing and code cleanup!

#### Future ideas:

* Nice facilities (modules) for concurrency/parallelism, using `std::thread`, etc. under the hood
* Instance names aren't used in generated C++11 code - possibly make them optional
* Compiler options for memory management
* `BigInt` via GNU GMP, possibly replacing current implementation of `Integer`
* Nicer generated local variable names if possible (push upstream to PureScript if successful)
* Stricter exports in C++ code
* Use C++ operator overloading where supported

#### Requirements

* Everything you need to build [PureScript](https://github.com/purescript/purescript)
* A C++11-capable toolchain, e.g. recent versions of clang, gcc
* Installed CMake is helpful (for the provided quickstart CMake file generated), though not required. You should be able to use your favorite C++ build system, tools, debuggers, etc., for the generated code.

#### Examples

**`hello.p11`**
```PureScript
module Main where

  import Debug.Trace

  main = do
    trace "Hello, world"
```

* `Main.hh`
```C++
// Generated by pcc version 0.6.8
#ifndef Main_H
#define Main_H

#include "Debug/Trace/Trace.hh"
#include "Prelude/Prelude.hh"
//
namespace Main {
    using namespace Debug_Trace;
    using namespace Prelude;
     
    auto main() -> data<Prelude::Unit>;
}
#endif // Main_H
```

* `Main.cc`
```C++
// Generated by pcc version 0.6.8
#define Main_CC

#include "Main/Main.hh"
//
namespace Main {
    auto main() -> data<Prelude::Unit> {
        return Debug_Trace::trace("Hello, world")();
    } 
}

int main(int, char *[]) {
    Main::main();
    return 0;
}
```
**`fib.p11`**
```PureScript
module Main where

  import Debug.Trace

  fib :: Int -> Int
  fib 0 = 0
  fib 1 = 1
  fib n = fib (n - 2) + fib (n - 1)

  main = do
    trace (show (fib 10))
```

  * `Main.cc`
```C++
// Generated by pcc version 0.6.8
#define Main_CC

#include "Main/Main.hh"
//
namespace Main {
    auto fib(int _34) -> int {
        if (_34 == 0) {
            return 0;
        }
        if (_34 == 1) {
            return 1;
        }
        return fib(_34 - 2) + fib(_34 - 1);
    } 
    auto main() -> data<Prelude::Unit> {
        return Debug_Trace::trace(show<int>(fib(10)))();
    } 
}

int main(int, char *[]) {
    Main::main();
    return 0;
}
```
