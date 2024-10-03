clear -all
check_cov -init -type all

# Setup environment
set wait_user true
set g_necessaryInstances {}
set g_totalCost 0
set cpf_revision 1.0
# Read in HDL files

# include source code
analyze -sv [ glob ./RV12/submodules/memory/rtl/verilog/*.sv]
analyze -sv [ glob ./RV12/submodules/ahb3lite_pkg/rtl/verilog/*.sv]
analyze -sv [ glob ./RV12/rtl/verilog/pkg/riscv_state_pkg.sv]
analyze -sv [ glob ./RV12/rtl/verilog/pkg/*.sv]
analyze -sv [ glob ./RV12/rtl/verilog/core/*.sv]
analyze -sv [ glob ./RV12/rtl/verilog/core/ex/*.sv]
analyze -sv [ glob ./RV12/rtl/verilog/core/cache/*.sv]
analyze -sv [ glob ./RV12/rtl/verilog/core/mmu/*.sv]
analyze -sv [ glob ./RV12/rtl/verilog/core/memory/*.sv]
analyze -sv [ glob ./RV12/rtl/verilog/ahb3lite/*.sv]
# analyze -sv [ glob RV12/top/riscv_top.sv]

# include assertion property
analyze -sv [ glob ./isa.sv]

elaborate -top riscv_top_ahb3lite

set_superlint_arithmetic_overflow_style both
set_superlint_arithmetic_overflow_enable_multiplication false

clock {HCLK}
reset ~HRESETn ~core.rst_ni
# Setup global environment
# Setup global clocks and resets
# Setup current task environment

stopat core.if_unit.parcel_valid
assume {core.if_unit.parcel_valid == 1'b1}

assume {core.du_stall == 1'b0}
assume {core.du_stall_if == 1'b0}
assume {core.du_re_rf == 1'b0}
assume {core.dbg_we_i == 1'b0}
assume {core.int_rf.du_we_rf_i == 0}
assume {core.cpu_state.du_we_csr_i == 0}

assume {dmem_ctrl_inst.pma_exception == 0}
stopat core.if_unit.parcel_exceptions
assume {core.if_unit.parcel_exceptions == 0}
assume {core.wb_exceptions == 0}
assume {core.id_unit.my_exceptions == 0}

# Fetched instruction always valid RV32I instruction
stopat core.if_unit.rv_instr
assume {
    core.if_unit.rv_instr[6:0] == 7'b0110111 ||     // LUI
    core.if_unit.rv_instr[6:0] == 7'b0010111 ||     // AUIPC
    core.if_unit.rv_instr[6:0] == 7'b1101111 ||     // JAL
    core.if_unit.rv_instr[6:0] == 7'b1100111 ||     // JALR

    (core.if_unit.rv_instr[6:0] == 7'b1100011       // B-type (Branch)
     && core.if_unit.rv_instr[14:12] != 3'b010  
     && core.if_unit.rv_instr[14:12] != 3'b011
    ) ||

    (core.if_unit.rv_instr[6:0] == 7'b0000011       // L-type
     && core.if_unit.rv_instr[14:12] != 3'b011
     && core.if_unit.rv_instr[14:12] != 3'b110
     && core.if_unit.rv_instr[14:12] != 3'b111
    ) ||

    (core.if_unit.rv_instr[6:0] == 7'b0100011       // S-type
     && core.if_unit.rv_instr[14:12] != 3'b000
     && core.if_unit.rv_instr[14:12] != 3'b001
     && core.if_unit.rv_instr[14:12] != 3'b010
    ) ||

    (core.if_unit.rv_instr[6:0] == 7'b0010011       // I-type 1
     && core.if_unit.rv_instr[14:12] != 3'b001
     && core.if_unit.rv_instr[14:12] != 3'b101
    ) ||

    (core.if_unit.rv_instr[6:0] == 7'b0010011       // I-type 2 (logit shift)
     && core.if_unit.rv_instr[31:25] == 7'b000
     && core.if_unit.rv_instr[14:12] == 3'b?01
    ) ||

    (core.if_unit.rv_instr[6:0] == 7'b0010011       // I-type 3 (arith shift)
     && core.if_unit.rv_instr[31:25] == 7'b0100000
     && core.if_unit.rv_instr[14:12] == 3'b101
    ) ||

    (core.if_unit.rv_instr[6:0] == 7'b0110011       // R-type 1
     && core.if_unit.rv_instr[31:25] == 7'b000
    ) ||

    (core.if_unit.rv_instr[6:0] == 7'b0110011       // R-type 2
     && core.if_unit.rv_instr[31:25] == 7'b0100000
     && (core.if_unit.rv_instr[14:12] == 3'b101 
         || core.if_unit.rv_instr[14:12] == 3'b000
        )
    ) ||
    
    (core.if_unit.rv_instr[6:0] == 7'b0001111       // FENCE, FENCE.TSO, PAUSE
     && core.if_unit.rv_instr[14:12] == 3'b000
    ) ||
   
    (core.if_unit.rv_instr[6:0] == 7'b1110011       // ECALL, EBREAK
     && core.if_unit.rv_instr[19:7] == 13'b0
     && (core.if_unit.rv_instr[31:20] == 12'd0 
         || core.if_unit.rv_instr[31:20] == 12'd1
        )
    )
};

task -set <embedded>
set_proofgrid_per_engine_max_local_jobs 15
set_prove_cache on

set_prove_time_limit 259200s

prove -all