clear -all
check_cov -init -type all

# Setup environment
set wait_user true
set g_necessaryInstances {}
set g_totalCost 0
set cpf_revision 1.0

# Read in HDL files
# include source code
check_cov -init -model { branch statement expression toggle functional } -type { stimuli coi proof bound }
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
analyze -sv [ glob ./property/fv_regfile.sv]
# analyze -sv [ glob RV12/top/riscv_top.sv]

set ANALYZE_FILE "analyze -sv property/isa.sv "
set ANALYZE_COMMAND $ANALYZE_FILE

# Define a function to set check flags and update ANALYZE_COMMAND
proc setCheckFlag {flagName flagValue} {
    global ANALYZE_COMMAND
    # Check the flag value and append the define string to ANALYZE_COMMAND if flagValue is 1
    if {$flagValue == 1} {
        set ANALYZE_COMMAND "${ANALYZE_COMMAND}+define+$flagName "
    }
}

# set check flag
setCheckFlag "CheckInstValidAssume" 0
setCheckFlag "RegFileStable" 0
setCheckFlag "PipeFollower" 0
setCheckFlag "ISA_GROUP_A" 1
    # Following Flag works only when "ISA_GROUP_A" set to 1
    setCheckFlag "xori" 0
    setCheckFlag "lb" 0
    setCheckFlag "blt" 0
    setCheckFlag "jal" 0
    setCheckFlag "auipc" 1

eval $ANALYZE_COMMAND

elaborate -top riscv_top_ahb3lite \
-bbox true \
-bbox_m biu_ahb3lite \
-bbox_m riscv_dmem_ctrl \
-bbox_m riscv_imem_ctrl \
-bbox_m riscv_du \
-bbox_m riscv_state1_10

# riscv_state is no used in rv32I, thus we can also bbox it
# Fix du port can further decrease complexity
assume {core.dbg_dato_o      == 0}     
assume {core.dbg_ack_o       == 0}    
assume {core.dbg_bp_o        == 0}   
assume {core.du_stall        == 0}   
assume {core.du_stall_if     == 0}      
assume {core.du_latch_nxt_pc == 0}          
assume {core.du_flush        == 0}   
assume {core.du_flush_cache  == 0}         
assume {core.du_re_rf        == 0}   
assume {core.du_we_rf        == 0}   
assume {core.du_we_frf       == 0}    
assume {core.du_re_csr       == 0}    
assume {core.du_we_csr       == 0}    
assume {core.du_we_pc        == 0}   
assume {core.du_addr         == 0}  
assume {core.du_dato         == 0}  
assume {core.du_ie           == 0}


# set_superlint_arithmetic_overflow_style both
config_rtlds -rule -enable -tag {ASG_AR_OVFL EXP_AR_OVFL}
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
assume {core.dbg_strb_i == 1'b0}
assume {core.int_rf.du_we_rf_i == 0}
assume {core.cpu_state.du_we_csr_i == 0}

# assume {dmem_ctrl_inst.pma_exception == 0}
stopat core.if_unit.parcel_exceptions
assume {core.if_unit.parcel_exceptions == 0}
assume {core.wb_exceptions == 0}
assume {core.id_unit.my_exceptions == 0}


# # All ahb transfer is always ready 
# assume {ibiu_inst.HREADY == 1}
# assume {dbiu_inst.HREADY == 1}

# # All ahb resp is ok (0), indicate no err
# assume {ibiu_inst.HRESP == 0}
# assume {ibiu_inst.HRESP == 0}

# cache always hit
# stopat imem_ctrl_inst.cache_blk.icache_inst.cache_hit
# assume {imem_ctrl_inst.cache_blk.icache_inst.cache_hit == 1}
# stopat dmem_ctrl_inst.cache_blk.dcache_inst.cache_hit
# assume {dmem_ctrl_inst.cache_blk.dcache_inst.cache_hit == 1}


# assume {core.dmem_ack_i == 0};
# assume {core.mem_stall[1] == 0};
# Fetched instruction always valid RV32I instruction
stopat core.if_unit.rv_instr

task -set <embedded>
set_proofgrid_per_engine_max_local_jobs 16
set_prove_cache on

set_prove_time_limit 259200s

prove -all
exec mkdir -p result
set current_date_time [exec date +%F_%T]
set result_file_name "result_${current_date_time}.jdb"
save -jdb ./result/${result_file_name} -capture_setup -capture_session_data