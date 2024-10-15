/*
*   Target DUV: riscv_rf
*   Specification:
*       1. It has 32 32-bit registers and the x0 is handled exceptionally.
*       2. It is "synchronous" read.(If REGOUT is 0)
*/

module fv_regfile
    import riscv_opcodes_pkg::*;
(
    // Common input
    input clk,
    input rst,

    // DUV signal input
    input [31:0] rf[32],

    //Register File read
    input rsd_t        rf_src1_i,
    input rsd_t        rf_src2_i,
    input       [31:0] rf_src1_q_o,
    input       [31:0] rf_src2_q_o,
    //Register File write
    input rsd_t        rf_dst_i,
    input       [31:0] rf_dst_d_i,
    input              rf_we_i,
    input              pd_stall_i,
    id_stall_i
);
    //////////////////// Property $ Sequence ////////////////////
    sequence value_0_flow_out(rsd_t rf_src_i);
        (~pd_stall_i && (rf_src_i == zero)) ##1 id_stall_i ##[0:$] ~id_stall_i;
    endsequence
    //////////////////// Assertion ////////////////////
    // verilog_format: off
    property write_correct(logic [31:0] duv_rf, rsd_t rf_dst, logic [4:0] rf_index);
        @(posedge clk) disable iff (rst)
        ~(pd_stall_i | id_stall_i) && (rf_dst == rf_index) && rf_we_i
        |=> ($past(rf_dst_d_i) == duv_rf);
    endproperty

    property reg_stable(logic [31:0] duv_rf, rsd_t rf_dst, logic [4:0] rf_index);
        @(posedge clk) disable iff (rst)
        ~(pd_stall_i | id_stall_i) && (rf_dst != rf_index) && rf_we_i
        |=> $stable(duv_rf);
    endproperty

    property x0_produce_0(rsd_t rf_src_i, logic [31:0] rf_src_q_o);
        @(posedge clk) disable iff (rst)
        value_0_flow_out(rf_src_i) |=> (rf_src_q_o == 32'd0);
    endproperty

    property other_read_correct(rsd_t rf_src_i, logic [31:0] rf_src_q_o);
        @(posedge clk) disable iff (rst)
        ~(pd_stall_i | id_stall_i) && (rf_src_i != zero)
        |=> ((rf[$past(rf_src_i)]) == rf_src_q_o);
    endproperty
    // verilog_format: on

    // x0 will always gives 0
    x0_gives_x0_at_src1 :
    assert property (x0_produce_0(rf_src1_i, rf_src1_q_o));
    x0_gives_x0_at_src2 :
    assert property (x0_produce_0(rf_src2_i, rf_src2_q_o));

    // Read Correct
    src1_read_correct :
    assert property (other_read_correct(rf_src1_i, rf_src1_q_o));
    src2_read_correct :
    assert property (other_read_correct(rf_src2_i, rf_src2_q_o));

    // All registers should reflect the written data after write operation
    genvar i;  // genvar
    generate
        for (i = 1; i < 32; i = i + 1) begin
            write_integrity :
            assert property (write_correct(rf[i], rf_dst_i, i));
        end
    endgenerate

    // All registers should remain the same when they are not written
    generate
        for (i = 1; i < 32; i = i + 1) begin
            stable :
            assert property (reg_stable(rf[i], rf_dst_i, i));
        end
    endgenerate

endmodule
