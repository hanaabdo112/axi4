module TOP #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 16,
    parameter MEMORY_DEPTH = 1024
) (
    input logic clk
);

    // AXI4 interface instance
    axi4_if #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .MEMORY_DEPTH(MEMORY_DEPTH)
    ) axi_bus (
        .ACLK(clk)
    );

    // DUT
    axi4 #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .MEMORY_DEPTH(MEMORY_DEPTH)
    ) u_design (
        .ACLK    (axi_bus.ACLK),
        .ARESETn (axi_bus.ARESETn),
        .AWADDR  (axi_bus.AWADDR),
        .AWLEN   (axi_bus.AWLEN),
        .AWSIZE  (axi_bus.AWSIZE),
        .AWVALID (axi_bus.AWVALID),
        .AWREADY (axi_bus.AWREADY),
        .WDATA   (axi_bus.WDATA),
        .WVALID  (axi_bus.WVALID),
        .WLAST   (axi_bus.WLAST),
        .WREADY  (axi_bus.WREADY),
        .BRESP   (axi_bus.BRESP),
        .BVALID  (axi_bus.BVALID),
        .BREADY  (axi_bus.BREADY),
        .ARADDR  (axi_bus.ARADDR),
        .ARLEN   (axi_bus.ARLEN),
        .ARSIZE  (axi_bus.ARSIZE),
        .ARVALID (axi_bus.ARVALID),
        .ARREADY (axi_bus.ARREADY),
        .RDATA   (axi_bus.RDATA),
        .RRESP   (axi_bus.RRESP),
        .RVALID  (axi_bus.RVALID),
        .RLAST   (axi_bus.RLAST),
        .RREADY  (axi_bus.RREADY)
    );

    // TB
    axi4_tb #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .MEMORY_DEPTH(MEMORY_DEPTH)
    ) u_tb (
        .bus(axi_bus)
    );

    // Assertions
    axi4_assertion #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .MEMORY_DEPTH(MEMORY_DEPTH)
    ) u_assertions (
        .bus(axi_bus)
    );

endmodule