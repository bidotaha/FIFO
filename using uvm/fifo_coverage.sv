package fifo_coverage_pkg;
import fifo_seq_item_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"  
  
  class fifo_coverage extends uvm_component;
    `uvm_component_utils(fifo_coverage)

    uvm_analysis_export #(fifo_seq_item) cov_export;
    uvm_tlm_analysis_fifo # (fifo_seq_item) cov_fifo;
    fifo_seq_item seq_item_cov;

        covergroup cvr_gp ;
            cover_wr_en : coverpoint seq_item_cov.wr_en ;
            cover_rd_en : coverpoint seq_item_cov.rd_en ;
            cover_wr_ack : coverpoint seq_item_cov.wr_ack ;
            cover_overflow : coverpoint seq_item_cov.overflow ;
            cover_underflow : coverpoint seq_item_cov.underflow ;
            cover_full : coverpoint seq_item_cov.full ;
            cover_empty : coverpoint seq_item_cov.empty ;
            cover_almostfull : coverpoint seq_item_cov.almostfull ;
            cover_almostempty : coverpoint seq_item_cov.almostempty ;

            label_cross1 : cross cover_wr_en , cover_rd_en , cover_wr_ack ;
            label_cross2 : cross cover_wr_en , cover_rd_en , cover_overflow ;
            label_cross3 : cross cover_wr_en , cover_rd_en , cover_underflow ;
            label_cross4 : cross cover_wr_en , cover_rd_en , cover_full ;
            label_cross5 : cross cover_wr_en , cover_rd_en , cover_empty ;
            label_cross6 : cross cover_wr_en , cover_rd_en , cover_almostfull ;
            label_cross7 : cross cover_wr_en , cover_rd_en , cover_almostempty ;
        endgroup 

  function new (string name = "fifo_cov" , uvm_component parent = null);
    super.new (name,parent);
    cvr_gp = new();
  endfunction 

    function void build_phase (uvm_phase phase);
    super.build_phase (phase);
    cov_export = new("cov_export",this);
    cov_fifo = new("cov_fifo",this);
  endfunction

  function void connect_phase(uvm_phase phase);
   super.connect_phase(phase);
   cov_export.connect(cov_fifo.analysis_export);
  endfunction  

  task run_phase (uvm_phase phase);
   super.run_phase(phase);
   forever begin
    cov_fifo.get(seq_item_cov);
    cvr_gp.sample();
   end
  endtask

  endclass 

  endpackage