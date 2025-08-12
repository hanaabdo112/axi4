module axi4_assertion #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 16,
    parameter MEMORY_DEPTH = 1024
) (
    axi4_if.assert_mp bus
);

    // Use reset to mask during reset and set default clock
    default disable iff (!bus.ARESETn);

    // Example properties
    property awvalid_stable;
        @(posedge bus.ACLK) bus.AWVALID && !bus.AWREADY |=> $stable(bus.AWADDR) && $stable(bus.AWLEN) && $stable(bus.AWSIZE);
    endproperty

    assert_awvalid_stable: assert property (awvalid_stable);
    cover_awvalid_stable:  cover  property (awvalid_stable);

    property awvalid_low_after_handshake;
        @(posedge bus.ACLK) bus.ARESETn && bus.AWVALID && bus.AWREADY |=> !bus.AWVALID;
    endproperty

    assert_awvalid_low_after_handshake: assert property (awvalid_low_after_handshake);
    cover_awvalid_low_after_handshake:  cover  property (awvalid_low_after_handshake);

    property wvalid_stable;
        @(posedge bus.ACLK) bus.ARESETn && bus.WVALID && !bus.WREADY |=> $stable(bus.WDATA) && $stable(bus.WLAST);
    endproperty

    assert_wvalid_stable: assert property (wvalid_stable);
    cover_wvalid_stable:  cover  property (wvalid_stable);

    // Ensure assertions are enabled for simulators that require it
    initial begin
        $asserton;
    end

endmodule