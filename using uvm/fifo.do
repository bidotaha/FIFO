vlib work
vlog -f fifo_files.list +cover -covercells
vsim -voptargs=+acc work.fifo_top -cover
add wave /fifo_top/fifoif/*
coverage save fifo_tb.ucdb -onexit 
run -all