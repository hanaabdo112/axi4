interface axi4_if #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 16,
    parameter MEMORY_DEPTH = 1024
    )(input bit ACLK);


    logic ARESETn;

    // AXI4 signals
    logic [ADDR_WIDTH-1:0] AWADDR;
    logic [7:0]            AWLEN;
    logic [2:0]            AWSIZE;
    logic                  AWVALID;
    logic                  AWREADY;

    logic [DATA_WIDTH-1:0] WDATA;
    logic                  WVALID;
    logic                  WLAST;
    logic                  WREADY;

    logic [1:0]            BRESP;
    logic                  BVALID;
    logic                  BREADY;

    logic [ADDR_WIDTH-1:0] ARADDR;
    logic [7:0]            ARLEN;
    logic [2:0]            ARSIZE;
    logic                  ARVALID;
    logic                  ARREADY;

    logic [DATA_WIDTH-1:0] RDATA;
    logic [1:0]            RRESP;
    logic                  RVALID;
    logic                  RLAST;
    logic                  RREADY;


    modport master (input ACLK, AWREADY, WREADY, BRESP, BVALID, ARREADY, RDATA, RRESP, RVALID, RLAST,
                    output ARESETn, AWADDR, AWLEN, AWSIZE, AWVALID, WDATA, WVALID, WLAST, BREADY, ARADDR, ARLEN, ARSIZE, ARVALID, RREADY);

    modport slave(input ACLK, ARESETn, AWADDR, AWLEN, AWSIZE, AWVALID, WDATA, WVALID, WLAST, BREADY, ARADDR, ARLEN, ARSIZE, ARVALID, RREADY,
                  output AWREADY, WREADY, BRESP, BVALID, ARREADY, RDATA, RRESP, RVALID, RLAST);

    
endinterface //interfacename