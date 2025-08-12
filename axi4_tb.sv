`include "transaction.sv"
module axi4_tb #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 16,
    parameter MEMORY_DEPTH = 1024
) (
    axi4_if.tb_mp bus
);

    // Local data used by TB
    logic [DATA_WIDTH-1:0] test_data ;
    logic [DATA_WIDTH-1:0] burst_data[];
    logic [DATA_WIDTH-1:0] read_data[];
    logic [DATA_WIDTH-1:0] current_addr;

    transaction stimulus;

    // Task for single write transaction
    task single_write(input logic [ADDR_WIDTH-1:0] addr, input logic [DATA_WIDTH-1:0] data);
        @(negedge bus.ACLK);
        bus.AWADDR = addr;
        bus.AWLEN = 0;  // Single transfer
        bus.AWSIZE = 2; // 4 bytes (32 bits)
        bus.AWVALID = 1;
        
        // Wait for address ready
        while(!bus.AWREADY) @(negedge bus.ACLK);
        @(negedge bus.ACLK);
        bus.AWVALID = 0;
        bus.BREADY = 1;
        // Data phase
        bus.WDATA = data;
        bus.WVALID = 1;
        bus.WLAST = 1;
        
        // Wait for data ready
        while(!bus.WREADY) @(negedge bus.ACLK);
        @(negedge bus.ACLK);
        bus.WVALID = 0;
        bus.WLAST = 0;
        
        // Response phase
       
        while(!bus.BVALID) @(negedge bus.ACLK);
        if(bus.BRESP != 2'b00) begin
            $display("[ERROR] Write transaction failed at address 0x%h, AWADDR 0x%h, response: %b", addr, bus.BRESP, bus.AWADDR);
        end
        @(negedge bus.ACLK);
        bus.BREADY = 0;
        
       // test_count++;
        $display("[TEST] Single write completed at address 0x%h, data: 0x%h", addr, data);
    endtask

    // Task for single read transaction
    task single_read(input logic [ADDR_WIDTH-1:0] addr, output logic [DATA_WIDTH-1:0] data);
        @(negedge bus.ACLK);
        bus.ARADDR = addr;
        bus.ARLEN = 0;  // Single transfer
        bus.ARSIZE = 2; // 4 bytes (32 bits)
        bus.ARVALID = 1;
        
        bus.RREADY = 1;
        // Wait for address ready
        while(!bus.ARREADY) @(negedge bus.ACLK);
        @(negedge bus.ACLK);
        bus.ARVALID = 0;
        
        // Data phase
        
        while(!bus.RVALID) @(negedge bus.ACLK);
        @(negedge bus.ACLK);
        data = bus.RDATA;
        if(bus.RRESP != 2'b00) begin
            $display("[ERROR] Read transaction failed at Time=%0t: address 0x%h, ARADDR 0x%h, response: %b",$time, addr, bus.ARADDR, bus.RRESP);
        end
        @(posedge bus.ACLK);
        bus.RREADY = 0;
        
        // test_count++;
        $display("[TEST] Single read completed at Time=%0t: address 0x%h, data: 0x%h",$time, addr, data);
    endtask

    // Task to verify memory content
    task verify_memory(input logic [ADDR_WIDTH-1:0] addr, input logic [DATA_WIDTH-1:0] expected_data);
        logic [DATA_WIDTH-1:0] read_data_local;
        
        single_read(addr, read_data_local);
        if(read_data_local !== expected_data) begin
            $display("[ERROR] Memory verification failed at Time=%0t: address 0x%h, Expected: 0x%h, Read: 0x%h",$time, 
                     addr, expected_data, read_data_local);
        end else begin
            $display("[Pass] Memory verified at Time=%0t: address 0x%h, Expected: 0x%h, data: 0x%h",$time, addr, expected_data, read_data_local);
        end
    endtask

    // Task for burst write transaction
    task burst_write(input logic [ADDR_WIDTH-1:0] addr, input int len, input logic [DATA_WIDTH-1:0] data[]);
        @(negedge bus.ACLK);
        bus.AWADDR = addr;
        bus.AWLEN = len - 1;  // Burst length is len+1
        bus.AWSIZE = 2;       // 4 bytes (32 bits)
        bus.AWVALID = 1;
        
        // Wait for address ready
        while(!bus.AWREADY) @(negedge bus.ACLK);
        @(negedge bus.ACLK);
        bus.AWVALID = 0;
        
        // Data phase
        for(int i = 0; i < len; i++) begin
            bus.WDATA = data[i];
            //$display("[DEBUG WRITE] Beat %0d: Addr=0x%h, Data=0x%h", i, addr + i*4, bus.WDATA);
            bus.WVALID = 1;
            bus.WLAST = (i == len-1);
            
            // Wait for data ready
            while(!bus.WREADY) @(negedge bus.ACLK);
            @(negedge bus.ACLK);
        end
         bus.WVALID = 0;
         bus.WLAST = 0;
        
        // Response phase
        bus.BREADY = 1;
        while(!bus.BVALID) @(negedge bus.ACLK);
        if(bus.BRESP != 2'b00) begin
            $display("[ERROR] Burst write transaction failed at Time=%0t: address 0x%h, response: %b",$time,  addr, bus.BRESP);
           
        end
        @(negedge bus.ACLK);
        bus.BREADY = 0;
        $display("[TEST] Burst write completed at Time=%0t: address 0x%h, length: %0d", $time, addr, len);
    endtask

    // Task for burst read transaction
    task burst_read(input logic [ADDR_WIDTH-1:0] addr, input int len, output logic [DATA_WIDTH-1:0] data[]);
        @(negedge bus.ACLK);
        
        bus.ARADDR = addr;
        bus.ARLEN = len - 1;
        data = new[len];  // Burst length is len+1
        bus.ARSIZE = 2;      // 4 bytes (32 bits)
        bus.ARVALID = 1;

        bus.RREADY = 1;
        // Wait for address ready
        while(!bus.ARREADY) @(negedge bus.ACLK);
        @(negedge bus.ACLK);
        bus.ARVALID = 0;
        
        // Data phase
        for(int i = 0; i < len; i++) begin
        while(!bus.RVALID) @(negedge bus.ACLK);
        @(negedge bus.ACLK);
        data[i] = bus.RDATA;
        //$display("[DEBUG READ] Beat %0d: Addr=0x%h, Data=0x%h, RRESP=%b", i, addr + i*4, data[i], bus.RRESP);
        if(bus.RRESP != 2'b00) begin
                $display("[ERROR] Read transaction failed at Time=%0t: beat %0d, address 0x%h, response: %b", $time, 
                         i, addr, bus.RRESP);
        end
        @(posedge bus.ACLK);
        end
        bus.RREADY = 0;
        $display("[TEST] Burst read completed at Time=%0t: address 0x%h, length: %0d, RDATA: %0h", $time, addr, len, bus.RDATA);
    endtask

    // Task to verify burst read data
    task verify_burst_read(input logic [ADDR_WIDTH-1:0] addr, input int len, 
                           input logic [DATA_WIDTH-1:0] expected_data[]);
        burst_read(addr, len, read_data);
        foreach(read_data[i]) begin
            current_addr = addr + i*4; // Address increment (4 bytes per word)
            if(read_data[i] !== expected_data[i]) begin
                $display("[ERROR] Burst read mismatch at Time=%0t: address 0x%h, beat %0d  Expected: 0x%h, Actual: 0x%h", $time, current_addr, i, expected_data[i], read_data[i]);
            end else begin
                $display("[PASS] Burst read match at Time=%0t: address 0x%h, beat %0d, data: 0x%h", 
                         $time, current_addr, i, read_data[i]);
            end
        end
    endtask

    task write_beyond_memory(input logic [ADDR_WIDTH-1:0] addr, input logic [DATA_WIDTH-1:0] data);
        @(negedge bus.ACLK);

        bus.AWADDR = addr;
        bus.AWLEN = 0;  // Single transfer
        bus.AWSIZE = 2; // 4 bytes (32 bits)
        bus.AWVALID = 1;
        
        // Wait for address ready
        while(!bus.AWREADY) @(negedge bus.ACLK);
        @(negedge bus.ACLK);
        bus.AWVALID = 0;
        bus.BREADY = 1;
        // Data phase
        bus.WDATA = data;
        bus.WVALID = 1;
        bus.WLAST = 1;
       
        // Wait for data ready
        while(!bus.WREADY) @(negedge bus.ACLK);
        @(negedge bus.ACLK);
        bus.WVALID = 0;
        bus.WLAST = 0;
        
        // Response phase
        
        while(!bus.BVALID) @(negedge bus.ACLK);
        if(bus.BRESP == 2'b10) begin
                $display("[ERROR] Expected error response for out-of-bound write, got: %b Time=%0t:", bus.BRESP, $time);
        end
        else begin
                $display("[TEST] Correct error response for out-of-bound write got: %b  Time=%0t:", bus.BRESP, $time);
            end
        @(negedge bus.ACLK);
        bus.BREADY = 0;
    endtask

    task read_beyond_memory(input logic [ADDR_WIDTH-1:0] addr, output logic [DATA_WIDTH-1:0] data);
        @(negedge bus.ACLK);
        bus.ARADDR = addr;
        bus.ARLEN = 0;  // Single transfer
        bus.ARSIZE = 2; // 4 bytes (32 bits)
        bus.ARVALID = 1;
        
        bus.RREADY = 1;
        // Wait for address ready
        while(!bus.ARREADY) @(negedge bus.ACLK);
        @(negedge bus.ACLK);
        bus.ARVALID = 0;
        
        // Data phase
        while(!bus.RVALID) @(negedge bus.ACLK);
        @(negedge bus.ACLK);
        data = bus.RDATA;
        
        if(bus.RRESP == 2'b10) begin
                $display("[ERROR] Expected error response for out-of-bound read,ARADDR = %0h,  RRESP: %b Time=%0t:",bus.ARADDR, bus.RRESP, $time);
        end
        else begin
                $display("[TEST] Correct error response for out-of-bound read RRESP: %b  Time=%0t:", bus.RRESP, $time);
            end
        @(posedge bus.ACLK);
        bus.RREADY = 0;
    endtask

    task randomize_transaction();
        stimulus = new();
        assert(stimulus.randomize());
        stimulus.cov.sample();
    endtask

    // Main TB process
    initial begin
        stimulus = new();
        bus.ARESETn = 0;
        #10ns;
        bus.ARESETn = 1;

        stimulus.awaddr_c.constraint_mode(0);
        stimulus.awlen_c.constraint_mode(0);
        write_beyond_memory(16'hfff1, 32'hA5A5A5A5);
        read_beyond_memory(16'hfff1, test_data);

        write_beyond_memory('d32767, 32'hBADDF00D);
        read_beyond_memory('d32767, test_data);

        stimulus.awaddr_c.constraint_mode(1);
        stimulus.awlen_c.constraint_mode(1);
        /////// randomization test
        repeat (500) begin
            randomize_transaction();
            // Check if the transaction is a single beat or burst
            if (stimulus.AWLEN == 8'h00) begin
                // Single beat transaction
                single_write(stimulus.AWADDR, stimulus.WDATA[0]);
                verify_memory(stimulus.AWADDR, stimulus.WDATA[0]);
            end else begin
                // Burst transaction
                burst_write(stimulus.AWADDR, stimulus.AWLEN, stimulus.WDATA);
                verify_burst_read(stimulus.AWADDR, stimulus.AWLEN, stimulus.WDATA);
            end
        end

        bus.ARESETn = 0;
        #10ns;
        bus.ARESETn = 1;

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