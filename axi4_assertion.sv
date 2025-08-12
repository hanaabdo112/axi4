module axi4_assertion #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 16,
    parameter MEMORY_DEPTH = 1024
)(
    axi4_if.assert_mp axi
);

    property awvalid_stable;
        @(posedge axi.ACLK) axi.AWVALID && !axi.AWREADY |=> $stable(axi.AWADDR) && $stable(axi.AWLEN) && $stable(axi.AWSIZE);
    endproperty

    assert_awvalid_stable: assert property (awvalid_stable);


    property awvalid_low_after_handshake;
        @(posedge axi.ACLK) axi.ARESETn && axi.AWVALID && axi.AWREADY |=> !axi.AWVALID;
    endproperty

    assert_awvalid_low_after_handshake: assert property (awvalid_low_after_handshake);


    property wvalid_stable;
        @(posedge axi.ACLK) axi.ARESETn && axi.WVALID && !axi.WREADY |=> $stable(axi.WDATA) && $stable(axi.WLAST);
    endproperty
    assert_wvalid_stable: assert property (wvalid_stable);




endmodule