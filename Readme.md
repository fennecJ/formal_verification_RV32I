# An SVA(SystemVerilog Assertion) based formal verification example on RV12 with a subset of RV32I ISA

This project implements an end-to-end verification[^1] approach for a CPU based on the RV32I ISA specification.

The CPU under test is a modified version of an older commit from the [RV12](https://github.com/RoaLogic/RV12) repository, included here under Roa Logic's Non-Commercial License Agreement for educational and research purposes.  

Verification focuses on a subset of RV32I instructions: `XORI`, `BLT`, `JAL`, `LB`, and `AUIPC`, representing the five main
instruction types (`I`, `B`, `J`, `L`, and `U`). Other instructions within the same type can likely be handled by referencing these examples.

**Running Formal Verification with JasperGold**

To perform formal verification with SystemVerilog Assertions, we use Cadence's JasperGold Formal Engine to execute our test suite, with TCL script `isa.tcl`.

## Detailed of implementation and result
The implementation can be find in directory `property`.
Details of our design considerations and implementation thoughts are discussed in [Report.md](./Report.md).

## Contribution Guide
Refer to [Contribute.md](./Contribute.md) if you want to contribute to this repo

## License

This repository contains code under multiple licenses:

1. **Roa Logic Code**  
   Portions of this repository include code from Roa Logic, specifically under the `RV12/` directory. These files are distributed under Roa Logic's Non-Commercial License Agreement and are strictly for non-commercial use. For more details, refer to [`ROA_LOGIC_LICENSE.md`](./RV12/ROA_LOGIC_LICENSE.md).


2. **MIT License**  
   All other parts of the code are licensed under the MIT License. See [`MIT_LICENSE.md`](./property/MIT_License.md) for details.

If you intend to use this repository, please ensure compliance with the respective licenses.

[^1]: [End-to-End Verification of ARM Processors with ISA-Formal](https://alastairreid.github.io/papers/cav2016_isa_formal.pdf)
