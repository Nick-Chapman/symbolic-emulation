# symbolic-emulation

Symbolic emulation to achieve machine code re-targeting.

Idea is to start with a very minimal ISA, somewhat inspired by 8080.
Code the emulation.

Then re-use the emulation code, but with symbolic execution, to generate a new program, which is not related to the details of the specific ISA, and so could potentially be emitted in any language, and recompiled. In addition the new program will completely avoid the overhead of an decoding and interpreting the instruction set at runtime.

Exactly how well this works will depend on the power of the original ISA; my plan is to start simple and then extend. The following issues will be challenging:

- indirect jumps
- runtime code generation
