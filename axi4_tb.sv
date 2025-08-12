`include "transaction.sv"
module axi4_tb #( 
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 16,
    parameter MEMORY_DEPTH = 1024
)(
    input logic clk,
    axi4_if.tb_mp axi
);

    // Clock and reset
    // Use clk for local timing; axi.ACLK is driven by TOP via interface

    // local aliases for brevity
    logic [DATA_WIDTH-1:0] test_data ;
    logic [DATA_WIDTH-1:0] burst_data[];
    logic [DATA_WIDTH-1:0] read_data[];
    logic [DATA_WIDTH-1:0] current_addr;

    transaction stimulus;

    // Clock generation moved to top; we just use clk

    // Task for single write transaction
    task single_write(input logic [ADDR_WIDTH-1:0] addr, input logic [DATA_WIDTH-1:0] data);
        @(negedge clk);
        axi.AWADDR = addr;
        axi.AWLEN = 0;  // Single transfer
        axi.AWSIZE = 2; // 4 bytes (32 bits)
        axi.AWVALID = 1;
        
        // Wait for address ready
        while(!axi.AWREADY) @(negedge clk);
        @(negedge clk);
        axi.AWVALID = 0;
        axi.BREADY = 1;
        // Data phase
        axi.WDATA = data;
        axi.WVALID = 1;
        axi.WLAST = 1;
        
        // Wait for data ready
        while(!axi.WREADY) @(negedge clk);
        @(negedge clk);
        axi.WVALID = 0;
        axi.WLAST = 0;
        
        // Response phase
       
        while(!axi.BVALID) @(negedge clk);
        if(axi.BRESP != 2'b00) begin
            $display("[ERROR] Write transaction failed at address 0x%h, AWADDR 0x%h, response: %b", addr, axi.BRESP, axi.AWADDR);
        end
        @(negedge clk);
        axi.BREADY = 0;
        
       // test_count++;
        $display("[TEST] Single write completed at address 0x%h, data: 0x%h", addr, data);
    endtask

    // Task for single read transaction
    task single_read(input logic [ADDR_WIDTH-1:0] addr, output logic [DATA_WIDTH-1:0] data);
        @(negedge clk);
        axi.ARADDR = addr;
        axi.ARLEN = 0;  // Single transfer
        axi.ARSIZE = 2; // 4 bytes (32 bits)
        axi.ARVALID = 1;
        
        axi.RREADY = 1;
        // Wait for address ready
        while(!axi.ARREADY) @(negedge clk);
        @(negedge clk);
        axi.ARVALID = 0;
        
        // Data phase
        
        while(!axi.RVALID) @(negedge clk);
        @(negedge clk);
        data = axi.RDATA;
        if(axi.RRESP != 2'b00) begin
            $display("[ERROR] Read transaction failed at Time=%0t: address 0x%h, ARADDR 0x%h, response: %b",$time, addr, axi.ARADDR, axi.RRESP);
        end
        @(posedge clk);
        axi.RREADY = 0;
        
        // test_count++;
        $display("[TEST] Single read completed at Time=%0t: address 0x%h, data: 0x%h",$time, addr, data);
    endtask

    // Task to verify memory content
    task verify_memory(input logic [ADDR_WIDTH-1:0] addr, input logic [DATA_WIDTH-1:0] expected_data);
        logic [DATA_WIDTH-1:0] read_data_l;
        single_read(addr, read_data_l);
        if(read_data_l !== expected_data) begin
            $display("[ERROR] Memory verification failed at Time=%0t: address 0x%h, Expected: 0x%h, Read: 0x%h",$time, 
                     addr, expected_data, read_data_l);
        end else begin
            $display("[Pass] Memory verified at Time=%0t: address 0x%h, Expected: 0x%h, data: 0x%h",$time, addr, expected_data, read_data_l);
        end
    endtask

    // Task for burst write transaction
    task burst_write(input logic [ADDR_WIDTH-1:0] addr, input int len, input logic [DATA_WIDTH-1:0] data[]);
        @(negedge clk);
        axi.AWADDR = addr;
        axi.AWLEN = len - 1;  // Burst length is len+1
        axi.AWSIZE = 2;       // 4 bytes (32 bits)
        axi.AWVALID = 1;
        // Wait for address ready
        while(!axi.AWREADY) @(negedge clk);
        @(negedge clk);
        axi.AWVALID = 0;
        // Data phase
        for(int i = 0; i < len; i++) begin
            axi.WDATA = data[i];
            axi.WVALID = 1;
            axi.WLAST = (i == len-1);
            // Wait for data ready
            while(!axi.WREADY) @(negedge clk);
            @(negedge clk);
        end
        axi.WVALID = 0;
        axi.WLAST = 0;
    endtask

    // Verify burst read helper (relies on single_read)
    task verify_burst_read(input logic [ADDR_WIDTH-1:0] base_addr, input int len, input logic [DATA_WIDTH-1:0] expected[]);
        logic [DATA_WIDTH-1:0] rd;
        for (int i = 0; i < len; i++) begin
            single_read(base_addr + i*4, rd);
            if (rd !== expected[i]) begin
                $display("[ERROR] Burst verify mismatch at idx %0d addr 0x%h exp=0x%h got=0x%h", i, base_addr + i*4, expected[i], rd);
            end
        end
    endtask

    task write_beyond_memory(input logic [ADDR_WIDTH-1:0] addr, input logic [DATA_WIDTH-1:0] data);
        // drive a write beyond legal memory results in SLVERR later on
        single_write(addr, data);
    endtask

    task read_beyond_memory(input logic [ADDR_WIDTH-1:0] addr, output logic [DATA_WIDTH-1:0] data);
        single_read(addr, data);
    endtask

    task randomize_transaction();
        stimulus = new();
        assert(stimulus.randomize());
        stimulus.cov.sample();
    endtask

    initial begin
        stimulus = new();
        axi.ARESETn = 0;
        #10ns;
        axi.ARESETn = 1;

        stimulus.awaddr_c.constraint_mode(0);
        stimulus.awlen_c.constraint_mode(0);
        write_beyond_memory(16'hfff1, 32'hA5A5A5A5);
        read_beyond_memory(16'hfff1, test_data);

        write_beyond_memory('d32767, 32'hBADDF00D);
        read_beyond_memory('d32767, test_data);

        stimulus.awaddr_c.constraint_mode(1);
        stimulus.awlen_c.constraint_mode(1);
        repeat (500) begin
            randomize_transaction();
            if (stimulus.AWLEN == 8'h00) begin
                single_write(stimulus.AWADDR, stimulus.WDATA[0]);
                verify_memory(stimulus.AWADDR, stimulus.WDATA[0]);
            end else begin
                burst_write(stimulus.AWADDR, stimulus.AWLEN, stimulus.WDATA);
                verify_burst_read(stimulus.AWADDR, stimulus.AWLEN, stimulus.WDATA);
            end
        end

        axi.ARESETn = 0;
        #10ns;
        axi.ARESETn = 1;

        stimulus.awaddr_c.constraint_mode(1);
        stimulus.awlen_c.constraint_mode(1);

        do begin
            randomize_transaction();
            if (stimulus.AWLEN == 8'h00) begin
                single_write(stimulus.AWADDR, stimulus.WDATA[0]);
                verify_memory(stimulus.AWADDR, stimulus.WDATA[0]);
            end else begin
                burst_write(stimulus.AWADDR, stimulus.AWLEN, stimulus.WDATA);
                verify_burst_read(stimulus.AWADDR, stimulus.AWLEN, stimulus.WDATA);
            end
        end while(stimulus.cov.get_coverage()<100.0);

        $stop;
    end

endmodule