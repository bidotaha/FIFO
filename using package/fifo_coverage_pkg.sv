package FIFO_coverage_pkg ;
import FIFO_transaction_pkg ::*;

  class FIFO_coverage ;
    FIFO_transaction  F_cvg_txn ;

  covergroup fifo_cvr_gp ;

            cover_wr_en : coverpoint F_cvg_txn.wr_en ;
            cover_rd_en : coverpoint F_cvg_txn.rd_en ;
            cover_wr_ack : coverpoint F_cvg_txn.wr_ack ;
            cover_overflow : coverpoint F_cvg_txn.overflow ;
            cover_underflow : coverpoint F_cvg_txn.underflow ;
            cover_full : coverpoint F_cvg_txn.full ;
            cover_empty : coverpoint F_cvg_txn.empty ;
            cover_almostfull : coverpoint F_cvg_txn.almostfull ;
            cover_almostempty : coverpoint F_cvg_txn.almostempty ;

            label_cross1 : cross cover_wr_en , cover_rd_en , cover_wr_ack ;
            label_cross2 : cross cover_wr_en , cover_rd_en , cover_overflow ;
            label_cross3 : cross cover_wr_en , cover_rd_en , cover_underflow ;
            label_cross4 : cross cover_wr_en , cover_rd_en , cover_full ;
            label_cross5 : cross cover_wr_en , cover_rd_en , cover_empty ;
            label_cross6 : cross cover_wr_en , cover_rd_en , cover_almostfull ;
            label_cross7 : cross cover_wr_en , cover_rd_en , cover_almostempty ;
        
  endgroup

  function new();
    fifo_cvr_gp = new();
  endfunction

  function void sample_data (input FIFO_transaction F_txn);
    F_cvg_txn = F_txn ;
    fifo_cvr_gp.sample();
  endfunction

  endclass
endpackage