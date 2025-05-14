import FIFO_transaction_pkg ::*;
import FIFO_scoreboard_pkg ::*;
import FIFO_coverage_pkg ::*;
import shared_pkg ::*;

module fifo_monitor (fifo_if.MONITOR fif);

FIFO_transaction FIFO_mon_txn  =new();
FIFO_scoreboard FIFO_mon_sb =new();
FIFO_coverage FIFO_mon_cov = new();

  initial begin
    forever begin
      @(negedge fif.clk);
      assert(FIFO_mon_txn.randomize());
      FIFO_mon_txn.rst_n       = fif.rst_n;
      FIFO_mon_txn.wr_en       = fif.wr_en;
      FIFO_mon_txn.rd_en       = fif.rd_en;
      FIFO_mon_txn.data_in     = fif.data_in;
      FIFO_mon_txn.data_out    = fif.data_out;
      FIFO_mon_txn.wr_ack      = fif.wr_ack;
      FIFO_mon_txn.overflow    = fif.overflow;
      FIFO_mon_txn.full        = fif.full;
      FIFO_mon_txn.empty       = fif.empty;
      FIFO_mon_txn.almostfull  = fif.almostfull;
      FIFO_mon_txn.almostempty = fif.almostempty;
      FIFO_mon_txn.underflow   = fif.underflow;
      fork
        begin
          FIFO_mon_cov.sample_data(FIFO_mon_txn);
        end

        begin
          FIFO_mon_sb.check_data(FIFO_mon_txn);
        end
      join
      if(test_finished) begin
        $display("Simulation Stopped : Error count = %0d , Correct count = %0d",error_count,correct_count);
        $stop ;      
      end
      
    end
  end


endmodule