
module chisel_top_4x4(clk, rst, config_, start, done, io_spl_rd_resp_0_ready, io_spl_rd_resp_0_valid, io_spl_rd_resp_0_bits, io_spl_rd_resp_1_ready, io_spl_rd_resp_1_valid, io_spl_rd_resp_1_bits, io_spl_rd_resp_2_ready, io_spl_rd_resp_2_valid, io_spl_rd_resp_2_bits, io_spl_rd_resp_3_ready, io_spl_rd_resp_3_valid, io_spl_rd_resp_3_bits, io_spl_rd_req_0_ready, io_spl_rd_req_0_valid, io_spl_rd_req_0_bits, io_spl_rd_req_1_ready, io_spl_rd_req_1_valid, io_spl_rd_req_1_bits, io_spl_rd_req_2_ready, io_spl_rd_req_2_valid, io_spl_rd_req_2_bits, io_spl_rd_req_3_ready, io_spl_rd_req_3_valid, io_spl_rd_req_3_bits, io_spl_wr_resp_0_ready, io_spl_wr_resp_0_valid, io_spl_wr_resp_0_bits, io_spl_wr_resp_1_ready, io_spl_wr_resp_1_valid, io_spl_wr_resp_1_bits, io_spl_wr_resp_2_ready, io_spl_wr_resp_2_valid, io_spl_wr_resp_2_bits, io_spl_wr_resp_3_ready, io_spl_wr_resp_3_valid, io_spl_wr_resp_3_bits, io_spl_wr_req_0_ready, io_spl_wr_req_0_valid, io_spl_wr_req_0_bits, io_spl_wr_req_1_ready, io_spl_wr_req_1_valid, io_spl_wr_req_1_bits, io_spl_wr_req_2_ready, io_spl_wr_req_2_valid, io_spl_wr_req_2_bits, io_spl_wr_req_3_ready, io_spl_wr_req_3_valid, io_spl_wr_req_3_bits
);
  input clk;
  input rst;
  input [319:0] config_;
  input          io_start,
  output         io_done,
  output         io_spl_rd_resp_0_ready,
  input          io_spl_rd_resp_0_valid,
  input  [527:0] io_spl_rd_resp_0_bits,
  output         io_spl_rd_resp_1_ready,
  input          io_spl_rd_resp_1_valid,
  input  [527:0] io_spl_rd_resp_1_bits,
  output         io_spl_rd_resp_2_ready,
  input          io_spl_rd_resp_2_valid,
  input  [527:0] io_spl_rd_resp_2_bits,
  output         io_spl_rd_resp_3_ready,
  input          io_spl_rd_resp_3_valid,
  input  [527:0] io_spl_rd_resp_3_bits,
  input          io_spl_rd_req_0_ready,
  output         io_spl_rd_req_0_valid,
  output [79:0]  io_spl_rd_req_0_bits,
  input          io_spl_rd_req_1_ready,
  output         io_spl_rd_req_1_valid,
  output [79:0]  io_spl_rd_req_1_bits,
  input          io_spl_rd_req_2_ready,
  output         io_spl_rd_req_2_valid,
  output [79:0]  io_spl_rd_req_2_bits,
  input          io_spl_rd_req_3_ready,
  output         io_spl_rd_req_3_valid,
  output [79:0]  io_spl_rd_req_3_bits,
  output         io_spl_wr_resp_0_ready,
  input          io_spl_wr_resp_0_valid,
  input  [16:0]  io_spl_wr_resp_0_bits,
  output         io_spl_wr_resp_1_ready,
  input          io_spl_wr_resp_1_valid,
  input  [16:0]  io_spl_wr_resp_1_bits,
  output         io_spl_wr_resp_2_ready,
  input          io_spl_wr_resp_2_valid,
  input  [16:0]  io_spl_wr_resp_2_bits,
  output         io_spl_wr_resp_3_ready,
  input          io_spl_wr_resp_3_valid,
  input  [16:0]  io_spl_wr_resp_3_bits,
  input          io_spl_wr_req_0_ready,
  output         io_spl_wr_req_0_valid,
  output [605:0] io_spl_wr_req_0_bits,
  input          io_spl_wr_req_1_ready,
  output         io_spl_wr_req_1_valid,
  output [605:0] io_spl_wr_req_1_bits,
  input          io_spl_wr_req_2_ready,
  output         io_spl_wr_req_2_valid,
  output [605:0] io_spl_wr_req_2_bits,
  input          io_spl_wr_req_3_ready,
  output         io_spl_wr_req_3_valid,
  output [605:0] io_spl_wr_req_3_bits
   
  HldAcceleratorMultiPortWrapper chiselAcc(
    .clock(clk), 
    .reset(~rst), 
    .io_config(config_),
    .io_spl_rd_req_0_ready(spl_rd_req_0_ready),
    .io_spl_rd_req_0_valid(spl_rd_req_0_valid),
    .io_spl_rd_req_0_bits(spl_rd_req_0_data),
    .io_spl_rd_resp_0_ready(spl_rd_resp_0_ready),
    .io_spl_rd_resp_0_valid(spl_rd_resp_0_valid),
    .io_spl_rd_resp_0_bits(spl_rd_resp_0_data),
    .io_spl_wr_req_0_ready(spl_wr_req_0_ready),
    .io_spl_wr_req_0_valid(spl_wr_req_0_valid),
    .io_spl_wr_req_0_bits(spl_wr_req_0_data),
    .io_spl_wr_resp_0_ready(spl_wr_resp_0_ready),
    .io_spl_wr_resp_0_valid(spl_wr_resp_0_valid),
    .io_spl_wr_resp_0_bits(spl_wr_resp_0_data),

    .io_spl_rd_req_1_ready(spl_rd_req_1_ready),
    .io_spl_rd_req_1_valid(spl_rd_req_1_valid),
    .io_spl_rd_req_1_bits(spl_rd_req_1_data),
    .io_spl_rd_resp_1_ready(spl_rd_resp_1_ready),
    .io_spl_rd_resp_1_valid(spl_rd_resp_1_valid),
    .io_spl_rd_resp_1_bits(spl_rd_resp_1_data),
    .io_spl_wr_req_1_ready(spl_wr_req_1_ready),
    .io_spl_wr_req_1_valid(spl_wr_req_1_valid),
    .io_spl_wr_req_1_bits(spl_wr_req_1_data),
    .io_spl_wr_resp_1_ready(spl_wr_resp_1_ready),
    .io_spl_wr_resp_1_valid(spl_wr_resp_1_valid),
    .io_spl_wr_resp_1_bits(spl_wr_resp_1_data),

    .io_spl_rd_req_2_ready(spl_rd_req_2_ready),
    .io_spl_rd_req_2_valid(spl_rd_req_2_valid),
    .io_spl_rd_req_2_bits(spl_rd_req_2_data),
    .io_spl_rd_resp_2_ready(spl_rd_resp_2_ready),
    .io_spl_rd_resp_2_valid(spl_rd_resp_2_valid),
    .io_spl_rd_resp_2_bits(spl_rd_resp_2_data),
    .io_spl_wr_req_2_ready(spl_wr_req_2_ready),
    .io_spl_wr_req_2_valid(spl_wr_req_2_valid),
    .io_spl_wr_req_2_bits(spl_wr_req_2_data),
    .io_spl_wr_resp_2_ready(spl_wr_resp_2_ready),
    .io_spl_wr_resp_2_valid(spl_wr_resp_2_valid),
    .io_spl_wr_resp_2_bits(spl_wr_resp_2_data),

    .io_spl_rd_req_3_ready(spl_rd_req_3_ready),
    .io_spl_rd_req_3_valid(spl_rd_req_3_valid),
    .io_spl_rd_req_3_bits(spl_rd_req_3_data),
    .io_spl_rd_resp_3_ready(spl_rd_resp_3_ready),
    .io_spl_rd_resp_3_valid(spl_rd_resp_3_valid),
    .io_spl_rd_resp_3_bits(spl_rd_resp_3_data),
    .io_spl_wr_req_3_ready(spl_wr_req_3_ready),
    .io_spl_wr_req_3_valid(spl_wr_req_3_valid),
    .io_spl_wr_req_3_bits(spl_wr_req_3_data),
    .io_spl_wr_resp_3_ready(spl_wr_resp_3_ready),
    .io_spl_wr_resp_3_valid(spl_wr_resp_3_valid),
    .io_spl_wr_resp_3_bits(spl_wr_resp_3_data),

    .io_done(done),
    .io_start(start)               
                   
  );
   
endmodule