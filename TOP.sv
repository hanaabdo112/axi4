module TOP #( 
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 16,
    parameter MEMORY_DEPTH = 1024
)(
    input logic clk
);

    // Instantiate the AXI4 interface with modports
    axi4_if #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .MEMORY_DEPTH(MEMORY_DEPTH)
    ) axi_bus (
        .ACLK(clk)
    );

    // DUT instance using dut modport
    axi4 #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .MEMORY_DEPTH(MEMORY_DEPTH)
    ) dut (
        .axi(axi_bus)
    );

    // Testbench instance using tb modport
    axi4_tb #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .MEMORY_DEPTH(MEMORY_DEPTH)
    ) tb (
        .clk(clk),
        .axi(axi_bus)
    );

    // Assertions instance using assertion modport
    axi4_assertion #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .MEMORY_DEPTH(MEMORY_DEPTH)
    ) assertions (
        .axi(axi_bus)
    );

endmodule