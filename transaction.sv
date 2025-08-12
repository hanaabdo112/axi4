class transaction;
    // Parameters
    parameter int DATA_WIDTH = 32;
    parameter int ADDR_WIDTH = 16;
    parameter int MEMORY_DEPTH = 1024;
    // Clock and reset
        //logic ARESETn;
    // AXI4 signals
    rand logic [ADDR_WIDTH-1:0] AWADDR;
    rand logic [7:0] AWLEN;
    logic [2:0] AWSIZE;
    rand logic [DATA_WIDTH-1:0] WDATA [];

    //constraints
    constraint awaddr_c { AWADDR inside {[0:MEMORY_DEPTH-1]}; }
    constraint awlen_c { 
        (AWLEN + AWADDR) < 1024;
     }

    //  constraint size_c {
    //     AWSIZE == 2;  // Only support 4-byte (32-bit) transfers
    // }

    constraint wdata_c {
        WDATA.size() == AWLEN + 1; // Ensure WDATA size matches AWLEN
     }

     covergroup cov;

     
        coverpoint AWADDR {
            bins addr_0 = {0};
            bins addr_low = {[1:255]};
            bins addr_mid = {[256:767]};
            bins addr_high = {[768:1023]};
            // bins addr_v_high = {[3072:4095]};
            // bins addr_invalid_low = {[4096:32767]};
            // bins addr_invalid_high = {[32768:(1 << ADDR_WIDTH)-1]};
            
        }
        coverpoint AWLEN {
            bins len_0 = {0};
            bins len_1 = {1};
            bins len_2_7 = {[2:7]};
            bins len_8_15 = {[8:15]};
            bins len_16_255 = {[16:255]};
        }
        /*coverpoint WDATA {
            bins data_0 = {32'h00000000};
            bins data_1 = {32'hFFFFFFFF};
            bins data_2_7 = {[32'h00000001:32'h0000FFFF]};
            bins data_8_15 = {[32'h00010000:32'hFFFF0000]};
        }*/
        coverpoint WDATA.size() {
            bins size_1 = {1};
            bins size_2_7 = {[2:7]};
            bins size_8_15 = {[8:15]};
            bins size_16_255 = {[16:255]};
        }

        // Cross coverage
        awlen_x_awaddr: cross AWLEN, AWADDR {
            option.cross_auto_bin_max = 0;
            bins small_burst_low_addr  = binsof(AWLEN.len_1) && binsof(AWADDR.addr_low) ||
                                binsof(AWLEN.len_2_7) && binsof(AWADDR.addr_low) || binsof(AWLEN.len_8_15) && binsof(AWADDR.addr_low);
    
            bins large_burst_high_addr = binsof(AWLEN.len_8_15) && binsof(AWADDR.addr_high) ||
                                 binsof(AWLEN.len_16_255) && binsof(AWADDR.addr_high);
            }

    endgroup : cov

    function new();
        // Constructor code here
        // Initialize the covergroup
        cov = new();
    endfunction //new()
endclass //transaction