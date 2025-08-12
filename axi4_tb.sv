`include "transaction.sv"
module axi4_tb ();
    // Parameters
    parameter DATA_WIDTH = 32;
    parameter ADDR_WIDTH = 16;
    parameter MEMORY_DEPTH = 1024;
   

    // Clock and reset
    logic ACLK;
    logic ARESETn;

    // AXI4 signals
    logic [ADDR_WIDTH-1:0] AWADDR;
    logic [7:0] AWLEN;
    logic [2:0] AWSIZE;
    logic AWVALID;
    logic AWREADY;

    logic [DATA_WIDTH-1:0] WDATA;
    logic WVALID;
    logic WLAST;
    logic WREADY;

    logic [1:0] BRESP;
    logic BVALID;
    logic BREADY;

    logic [ADDR_WIDTH-1:0] ARADDR;
    logic [7:0] ARLEN;
    logic [2:0] ARSIZE;
    logic ARVALID;
    logic ARREADY;

    logic [DATA_WIDTH-1:0] RDATA;
    logic [1:0] RRESP;
    logic RVALID;
    logic RLAST;
    logic RREADY;


    logic [DATA_WIDTH-1:0] test_data ;
    logic [DATA_WIDTH-1:0] burst_data[];
    logic [DATA_WIDTH-1:0] read_data[];
    logic [DATA_WIDTH-1:0] current_addr;

    transaction stimulus;

    axi4_assertion ass(.*);


    // Clock generation
    initial begin
        ACLK = 0;
        forever #5 ACLK = ~ACLK;
    end

     // Instantiate DUT
    axi4 #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .MEMORY_DEPTH(MEMORY_DEPTH)
    ) dut (
        .ACLK(ACLK),
        .ARESETn(ARESETn),
        .AWADDR(AWADDR),
        .AWLEN(AWLEN),
        .AWSIZE(AWSIZE),
        .AWVALID(AWVALID),
        .AWREADY(AWREADY),
        .WDATA(WDATA),
        .WVALID(WVALID),
        .WLAST(WLAST),
        .WREADY(WREADY),
        .BRESP(BRESP),
        .BVALID(BVALID),
        .BREADY(BREADY),
        .ARADDR(ARADDR),
        .ARLEN(ARLEN),
        .ARSIZE(ARSIZE),
        .ARVALID(ARVALID),
        .ARREADY(ARREADY),
        .RDATA(RDATA),
        .RRESP(RRESP),
        .RVALID(RVALID),
        .RLAST(RLAST),
        .RREADY(RREADY)
    );

     // Task for single write transaction
    task single_write(input logic [ADDR_WIDTH-1:0] addr, input logic [DATA_WIDTH-1:0] data);
        @(negedge ACLK);
        AWADDR = addr;
        AWLEN = 0;  // Single transfer
        AWSIZE = 2; // 4 bytes (32 bits)
        AWVALID = 1;
        
        // Wait for address ready
        while(!AWREADY) @(negedge ACLK);
        @(negedge ACLK);
        AWVALID = 0;
        BREADY = 1;
        // Data phase
        WDATA = data;
        WVALID = 1;
        WLAST = 1;
        
        // Wait for data ready
        while(!WREADY) @(negedge ACLK);
        @(negedge ACLK);
        WVALID = 0;
        WLAST = 0;
        
        // Response phase
       
        while(!BVALID) @(negedge ACLK);
        if(BRESP != 2'b00) begin
            $display("[ERROR] Write transaction failed at address 0x%h, AWADDR 0x%h, response: %b", addr, BRESP, AWADDR);
        end
        @(negedge ACLK);
        BREADY = 0;
        
       // test_count++;
        $display("[TEST] Single write completed at address 0x%h, data: 0x%h", addr, data);
    endtask

    // Task for single read transaction
    task single_read(input logic [ADDR_WIDTH-1:0] addr, output logic [DATA_WIDTH-1:0] data);
        @(negedge ACLK);
        ARADDR = addr;
        ARLEN = 0;  // Single transfer
        ARSIZE = 2; // 4 bytes (32 bits)
        ARVALID = 1;
        
        RREADY = 1;
        // Wait for address ready
        while(!ARREADY) @(negedge ACLK);
        @(negedge ACLK);
        ARVALID = 0;
        
        // Data phase
        
        while(!RVALID) @(negedge ACLK);
        @(negedge ACLK);
        data = RDATA;
        if(RRESP != 2'b00) begin
            $display("[ERROR] Read transaction failed at Time=%0t: address 0x%h, ARADDR 0x%h, response: %b",$time, addr, ARADDR, RRESP);
        end
        @(posedge ACLK);
        RREADY = 0;
        
        // test_count++;
        $display("[TEST] Single read completed at Time=%0t: address 0x%h, data: 0x%h",$time, addr, data);
    endtask


    // Task to verify memory content
    task verify_memory(input logic [ADDR_WIDTH-1:0] addr, input logic [DATA_WIDTH-1:0] expected_data);
        logic [DATA_WIDTH-1:0] read_data;
        
        single_read(addr, read_data);
        if(read_data !== expected_data) begin
            $display("[ERROR] Memory verification failed at Time=%0t: address 0x%h, Expected: 0x%h, Read: 0x%h",$time, 
                     addr, expected_data, read_data);
            // error_count++;
            // test_pass = 0;
        end else begin
            $display("[Pass] Memory verified at Time=%0t: address 0x%h, Expected: 0x%h, data: 0x%h",$time, addr, expected_data, read_data);
        end
    endtask



    // Task for burst write transaction
    task burst_write(input logic [ADDR_WIDTH-1:0] addr, input int len, input logic [DATA_WIDTH-1:0] data[]);
        @(negedge ACLK);
        AWADDR = addr;
        AWLEN = len - 1;  // Burst length is len+1
        AWSIZE = 2;       // 4 bytes (32 bits)
        AWVALID = 1;
        
        // Wait for address ready
        while(!AWREADY) @(negedge ACLK);
        @(negedge ACLK);
        AWVALID = 0;
        
        // Data phase
        for(int i = 0; i < len; i++) begin
            WDATA = data[i];
            //$display("[DEBUG WRITE] Beat %0d: Addr=0x%h, Data=0x%h", i, addr + i*4, WDATA);
            WVALID = 1;
            WLAST = (i == len-1);
            
            // Wait for data ready
            while(!WREADY) @(negedge ACLK);
            @(negedge ACLK);
        end
         WVALID = 0;
         WLAST = 0;
        
        // Response phase
        BREADY = 1;
        while(!BVALID) @(negedge ACLK);
        if(BRESP != 2'b00) begin
            $display("[ERROR] Burst write transaction failed at Time=%0t: address 0x%h, response: %b",$time,  addr, BRESP);
           
        end
        @(negedge ACLK);
        BREADY = 0;
        $display("[TEST] Burst write completed at Time=%0t: address 0x%h, length: %0d", $time, addr, len);
    endtask


    // Task for burst read transaction
    task burst_read(input logic [ADDR_WIDTH-1:0] addr, input int len, output logic [DATA_WIDTH-1:0] data[]);
        @(negedge ACLK);
        
        ARADDR = addr;
        ARLEN = len - 1;
        data = new[len];  // Burst length is len+1
        ARSIZE = 2;      // 4 bytes (32 bits)
        ARVALID = 1;

        RREADY = 1;
        // Wait for address ready
        while(!ARREADY) @(negedge ACLK);
        @(negedge ACLK);
        ARVALID = 0;
        
        // Data phase
        for(int i = 0; i < len; i++) begin
        while(!RVALID) @(negedge ACLK);
        @(negedge ACLK);
        data[i] = RDATA;
        //$display("[DEBUG READ] Beat %0d: Addr=0x%h, Data=0x%h, RRESP=%b", i, addr + i*4, data[i], RRESP);
        

       if(RRESP != 2'b00) begin
                $display("[ERROR] Read transaction failed at Time=%0t: beat %0d, address 0x%h, response: %b", $time, 
                         i, addr, RRESP);
        end

         @(posedge ACLK);
        end
        RREADY = 0;
        $display("[TEST] Burst read completed at Time=%0t: address 0x%h, length: %0d, RDATA: %0h", $time, addr, len, RDATA);
    endtask


    // Task to verify burst read data
task verify_burst_read(input logic [ADDR_WIDTH-1:0] addr, input int len, 
                       input logic [DATA_WIDTH-1:0] expected_data[]);

    // Verify each word in the burst
    //for(int i = 0; i < len; i++) begin
    
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
        @(negedge ACLK);

        AWADDR = addr;
         //stimulus.cov.sample();
        AWLEN = 0;  // Single transfer
        AWSIZE = 2; // 4 bytes (32 bits)
        AWVALID = 1;
        
        // Wait for address ready
        while(!AWREADY) @(negedge ACLK);
        @(negedge ACLK);
        AWVALID = 0;
        BREADY = 1;
        // Data phase
        WDATA = data;
        WVALID = 1;
        WLAST = 1;
       
        // Wait for data ready
        while(!WREADY) @(negedge ACLK);
        @(negedge ACLK);
        WVALID = 0;
        WLAST = 0;
        
        // Response phase
       
        while(!BVALID) @(negedge ACLK);
        if(BRESP == 2'b10) begin
                $display("[ERROR] Expected error response for out-of-bound write, got: %b Time=%0t:", BRESP, $time);
        end
        else begin
                $display("[TEST] Correct error response for out-of-bound write got: %b  Time=%0t:", BRESP, $time);
            end
        @(negedge ACLK);
        BREADY = 0;
        
       //$display("[TEST] Correct error response for out-of-bound write got: %b", BRESP);
    endtask


    task read_beyond_memory(input logic [ADDR_WIDTH-1:0] addr, output logic [DATA_WIDTH-1:0] data);
        @(negedge ACLK);
        ARADDR = addr;
       // stimulus.cov.sample();
        ARLEN = 0;  // Single transfer
        ARSIZE = 2; // 4 bytes (32 bits)
        ARVALID = 1;
        
        RREADY = 1;
        // Wait for address ready
        while(!ARREADY) @(negedge ACLK);
        @(negedge ACLK);
        ARVALID = 0;
        
        // Data phase
        
        while(!RVALID) @(negedge ACLK);
        @(negedge ACLK);
        data = RDATA;
        
        if(RRESP == 2'b10) begin
                $display("[ERROR] Expected error response for out-of-bound read,ARADDR = %0h,  RRESP: %b Time=%0t:",ARADDR, RRESP, $time);
        end
        else begin
                $display("[TEST] Correct error response for out-of-bound read RRESP: %b  Time=%0t:", RRESP, $time);
            end
        @(posedge ACLK);
        RREADY = 0;
        
        // test_count++;
       // $display("[TEST] Single read completed at Time=%0t: address 0x%h, data: 0x%h",$time, addr, data);
    endtask


task randomize_transaction();
    stimulus = new();
    assert(stimulus.randomize());
    stimulus.cov.sample();
    // Use the randomized transaction
endtask


     initial begin
        stimulus = new();
        ARESETn = 0;
        #10ns;
        ARESETn = 1;
         // Sample the covergroup after reset
       /*// Test 1: Simple write and read back
        begin
           // logic [DATA_WIDTH-1:0] test_data = 32'hA5A5A5A5;
            single_write(16'h0000, 32'hA5A5A5A5);
            //#20;
            verify_memory(16'h0000, 32'hA5A5A5A5);
        end

        // // Test 2: Multiple single writes and reads
        // for(int i = 0; i < 10; i++) begin
        //     test_data = $urandom();
        //     single_write(16'h0010 + i*4, test_data);
            
        //     verify_memory(16'h0010 + i*4, test_data);
        // end

        // Test 3: Burst write and read
        begin
            // Initialize burst_data
            burst_data = new[8];
            foreach(burst_data[i]) begin
                burst_data[i] = $urandom();
                $display("Burst data[%0d] = 0x%h", i, burst_data[i]);
            end
            
            burst_write(16'h0100, 8, burst_data);
            
            read_data = new[8];
           // burst_read(16'h0100, 8, read_data);

            // // Verify burst read data
             verify_burst_read(16'h0100, 8, burst_data);
        end
        #20;
        */
    

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
        //burst_data = new[stimulus.AWLEN + 1];
        burst_write(stimulus.AWADDR, stimulus.AWLEN, stimulus.WDATA);
        verify_burst_read(stimulus.AWADDR, stimulus.AWLEN, stimulus.WDATA);
    end
    end

    
    ARESETn = 0;
    #10ns;
    ARESETn = 1;

    stimulus.awaddr_c.constraint_mode(1);
    stimulus.awlen_c.constraint_mode(1);


    
    do begin
     randomize_transaction();
    // Check if the transaction is a single beat or burst
    if (stimulus.AWLEN == 8'h00) begin
        // Single beat transaction
        single_write(stimulus.AWADDR, stimulus.WDATA[0]);
        verify_memory(stimulus.AWADDR, stimulus.WDATA[0]);
    end else begin
        // Burst transaction
        //burst_data = new[stimulus.AWLEN + 1];
        burst_write(stimulus.AWADDR, stimulus.AWLEN, stimulus.WDATA);
        verify_burst_read(stimulus.AWADDR, stimulus.AWLEN, stimulus.WDATA);
    end
      end while(stimulus.cov.get_coverage()<100.0);
   
   
    $stop;

     end
    

endmodule