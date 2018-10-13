package simplevote_1.com.cyberpointllc.stac.webmaster.handler;

import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkSessionService;

public class LogoutGuideCreator {
    private NetworkSessionService networkSessionService;

    public LogoutGuideCreator setNetworkSessionService(NetworkSessionService networkSessionService) {
        this.networkSessionService = networkSessionService;
        return this;
    }

    public LogoutGuide formLogoutGuide() {
        return new LogoutGuide(networkSessionService);
    }
}