import FIFO_transaction_pkg ::*;
import shared_pkg::*;

module fifo_tb (fifo_if.TEST fif);

  FIFO_transaction test_txn = new();
  
  initial begin
    fif.rst_n = 0 ;
    repeat(2) @(negedge fif.clk);
    repeat(2000) begin
    assert(test_txn.randomize());
    fif.rst_n = test_txn.rst_n ;
    fif.wr_en = test_txn.wr_en ;
    fif.rd_en = test_txn.rd_en ;
    fif.data_in = test_txn.data_in ;
    repeat(2) @(negedge fif.clk);
    end
    test_finished = 1 ;
  end
endmodule