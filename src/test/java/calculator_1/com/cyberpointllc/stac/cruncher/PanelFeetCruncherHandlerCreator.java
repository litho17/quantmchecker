package calculator_1.com.cyberpointllc.stac.cruncher;

import calculator_1.com.cyberpointllc.stac.netcontroller.NetSessionService;

public class PanelFeetCruncherHandlerCreator {
    private NetSessionService netSessionService;

    public PanelFeetCruncherHandlerCreator fixNetSessionService(NetSessionService netSessionService) {
        this.netSessionService = netSessionService;
        return this;
    }

    public PanelFeetCruncherHandler composePanelFeetCruncherHandler() {
        return new PanelFeetCruncherHandler(netSessionService);
    }
}