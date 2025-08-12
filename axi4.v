module axi4 #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 16,
    parameter MEMORY_DEPTH = 1024
)(
    axi4_if.dut_mp axi
);


    // Internal memory signals
    reg mem_en, mem_we;
    reg [$clog2(MEMORY_DEPTH)-1:0] mem_addr;
    reg [DATA_WIDTH-1:0] mem_wdata;
    wire [DATA_WIDTH-1:0] mem_rdata;

    // Address and burst management
    reg [ADDR_WIDTH-1:0] write_addr, read_addr;
    reg [7:0] write_burst_len, read_burst_len;
    reg [7:0] write_burst_cnt, read_burst_cnt;
    reg [2:0] write_size, read_size;
    
    wire [ADDR_WIDTH-1:0] write_addr_incr,read_addr_incr;
    
    
    
    // Address increment calculation
    assign  write_addr_incr = (1 << write_size);
    assign  read_addr_incr  = (1 << read_size);
    
    // Address boundary check (4KB boundary = 12 bits)
    wire write_boundary_cross = ((write_addr & 12'hFFF) + (write_burst_len << write_size)) > 12'hFFF;
    wire read_boundary_cross = ((read_addr & 12'hFFF) + (read_burst_len << read_size)) > 12'hFFF;
    
    // Address range check
    wire write_addr_valid = (write_addr >> 2) < MEMORY_DEPTH;
    wire read_addr_valid = (read_addr >> 2) < MEMORY_DEPTH;

    // Memory instance
    axi4_memory #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH($clog2(MEMORY_DEPTH)),
        .DEPTH(MEMORY_DEPTH)
    ) mem_inst (
        .clk(axi.ACLK),
        .rst_n(axi.ARESETn),
        .mem_en(mem_en),
        .mem_we(mem_we),
        .mem_addr(mem_addr),
        .mem_wdata(mem_wdata),
        .mem_rdata(mem_rdata)
    );

    // FSM states
    reg [2:0] write_state;
    localparam W_IDLE = 3'd0,
               W_ADDR = 3'd1,
               W_DATA = 3'd2,
               W_RESP = 3'd3;

    reg [2:0] read_state;
    localparam R_IDLE = 3'd0,
               R_ADDR = 3'd1,
               R_DATA = 3'd2;

    // Registered memory read data for timing
    reg [DATA_WIDTH-1:0] mem_rdata_reg;

    always @(posedge axi.ACLK or negedge axi.ARESETn) begin
        if (!axi.ARESETn) begin
            // Reset all outputs
            axi.AWREADY <= 1'b1;  // Ready to accept address
            axi.WREADY <= 1'b0;
            axi.BVALID <= 1'b0;
            axi.BRESP <= 2'b00;
            
            axi.ARREADY <= 1'b1;  // Ready to accept address
            axi.RVALID <= 1'b0;
            axi.RRESP <= 2'b00;
            axi.RDATA <= {DATA_WIDTH{1'b0}};
            axi.RLAST <= 1'b0;
            
            // Reset internal state
            write_state <= W_IDLE;
            read_state <= R_IDLE;
            mem_en <= 1'b0;
            mem_we <= 1'b0;
            mem_addr <= {$clog2(MEMORY_DEPTH){1'b0}};
            mem_wdata <= {DATA_WIDTH{1'b0}};
            
            // Reset address tracking
            write_addr <= {ADDR_WIDTH{1'b0}};
            read_addr <= {ADDR_WIDTH{1'b0}};
            write_burst_len <= 8'b0;
            read_burst_len <= 8'b0;
            write_burst_cnt <= 8'b0;
            read_burst_cnt <= 8'b0;
            write_size <= 3'b0;
            read_size <= 3'b0;
            
            mem_rdata_reg <= {DATA_WIDTH{1'b0}};
            
        end else begin
            // Default memory disable
            mem_en <= 1'b0;
            mem_we <= 1'b0;

            // --------------------------
            // Write Channel FSM
            // --------------------------
            case (write_state)
                W_IDLE: begin
                    axi.AWREADY <= 1'b1;
                    axi.WREADY <= 1'b0;
                    axi.BVALID <= 1'b0;
                    
                    if (axi.AWVALID && axi.AWREADY) begin
                        // Capture address phase information
                        write_addr <= axi.AWADDR;
                        write_burst_len <= axi.AWLEN;
                        write_burst_cnt <= axi.AWLEN;
                        write_size <= axi.AWSIZE;
                        
                        axi.AWREADY <= 1'b0;
                        write_state <= W_ADDR;
                    end
                end
                
                W_ADDR: begin
                    // Transition to data phase
                    axi.WREADY <= 1'b1;
                    write_state <= W_DATA;
                end
                
                W_DATA: begin
                    if (axi.WVALID && axi.WREADY) begin
                        // Check if address is valid
                        if (write_addr_valid && !write_boundary_cross) begin
                            // Perform write operation
                            mem_en <= 1'b1;
                            mem_we <= 1'b1;
                            mem_addr <= write_addr >> 2;  // Convert to word address
                            mem_wdata <= axi.WDATA;
                        end
                        
                        // Check for last transfer
                        if (axi.WLAST || write_burst_cnt == 0) begin
                            axi.WREADY <= 1'b0;
                            write_state <= W_RESP;
                            
                            // Set response - delayed until write completion
                            if (!write_addr_valid || write_boundary_cross) begin
                                axi.BRESP <= 2'b10;  // SLVERR
                            end else begin
                                axi.BRESP <= 2'b00;  // OKAY
                            end
                            axi.BVALID <= 1'b1;
                        end else begin
                            // Continue burst - increment address
                            write_addr <= write_addr + write_addr_incr;
                            write_burst_cnt <= write_burst_cnt - 1'b1;
                        end
                    end
                end
                
                W_RESP: begin
                    if (axi.BREADY && axi.BVALID) begin
                        axi.BVALID <= 1'b0;
                    end
                end
            endcase

            // --------------------------
            // Read Channel FSM
            // --------------------------
            case (read_state)
                R_IDLE: begin
                    axi.ARREADY <= 1'b1;
                    axi.RVALID <= 1'b0;
                    axi.RLAST <= 1'b0;
                    
                    if (axi.ARVALID && axi.ARREADY) begin
                        // Capture read address phase information
                        read_addr <= axi.ARADDR;
                        read_burst_len <= axi.ARLEN;
                        read_burst_cnt <= axi.ARLEN;
                        read_size <= axi.ARSIZE;
                        
                        axi.ARREADY <= 1'b0;
                        read_state <= R_ADDR;
                    end
                end
                
                R_ADDR: begin
                    // Transition to data phase
                    axi.RVALID <= 1'b1;
                    read_state <= R_DATA;
                end
                
                R_DATA: begin
                    if (axi.RVALID && axi.RREADY) begin
                        // Check if address is valid
                        if (read_addr_valid && !read_boundary_cross) begin
                            // Read operation
                            mem_en <= 1'b1;
                            mem_we <= 1'b0;
                            mem_addr <= read_addr >> 2;  // Convert to word address
                            mem_rdata_reg <= mem_rdata;
                            axi.RDATA <= mem_rdata_reg;
                            axi.RRESP <= 2'b00;  // OKAY
                        end else begin
                            axi.RDATA <= {DATA_WIDTH{1'b0}};
                            axi.RRESP <= 2'b10;  // SLVERR
                        end

                        // Check for last transfer
                        if (read_burst_cnt == 0) begin
                            axi.RLAST <= 1'b1;
                            // End of burst
                            if (axi.RVALID && axi.RREADY) begin
                                axi.RVALID <= 1'b0;
                                axi.RLAST <= 1'b0;
                                read_state <= R_IDLE;
                            end
                        end else begin
                            // Continue burst - increment address
                            read_addr <= read_addr + read_addr_incr;
                            read_burst_cnt <= read_burst_cnt - 1'b1;
                        end
                    end
                end
            endcase
        end
    end

endmodule