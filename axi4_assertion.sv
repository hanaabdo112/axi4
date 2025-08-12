module axi4_assertion #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 16,
    parameter MEMORY_DEPTH = 1024
)(
    input logic                     ACLK,
    input logic                     ARESETn,

    // Write address channel
    input logic [ADDR_WIDTH-1:0]    AWADDR,
    input logic [7:0]               AWLEN,
    input logic [2:0]               AWSIZE,
    input logic                     AWVALID,
    input logic                     AWREADY,

    // Write data channel
    input logic [DATA_WIDTH-1:0]    WDATA,
    input logic                     WVALID,
    input logic                     WLAST,
    input logic                     WREADY,

    // Write response channel
    input logic[1:0]                BRESP,
    input logic                     BVALID,
    input logic                     BREADY,

    // Read address channel
    input logic [ADDR_WIDTH-1:0]    ARADDR,
    input logic [7:0]               ARLEN,
    input logic [2:0]               ARSIZE,
    input logic                     ARVALID,
    input logic                     ARREADY,

    // Read data channel
    input logic[DATA_WIDTH-1:0]     RDATA,
    input logic[1:0]                RRESP,
    input logic                     RVALID,
    input logic                     RLAST,
    input logic                     RREADY
);

    property awvalid_stable;
        @(posedge ACLK) AWVALID && !AWREADY |=> $stable(AWADDR) && $stable(AWLEN) && $stable(AWSIZE);
    endproperty

    assert_awvalid_stable: assert property (awvalid_stable);


    property awvalid_low_after_handshake;
        @(posedge ACLK) ARESETn && AWVALID && AWREADY |=> !AWVALID;
    endproperty

    assert_awvalid_low_after_handshake: assert property (awvalid_low_after_handshake);


    property wvalid_stable;
        @(posedge ACLK) ARESETn && WVALID && !WREADY |=> $stable(WDATA) && $stable(WLAST);
    endproperty
    assert_wvalid_stable: assert property (wvalid_stable);




    
endmodule