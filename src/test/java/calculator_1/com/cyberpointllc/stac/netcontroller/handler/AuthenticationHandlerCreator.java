package calculator_1.com.cyberpointllc.stac.netcontroller.handler;

public class AuthenticationHandlerCreator {
    private String redirectResponseWalk;

    public AuthenticationHandlerCreator assignRedirectResponseWalk(String redirectResponseWalk) {
        this.redirectResponseWalk = redirectResponseWalk;
        return this;
    }

    public AuthenticationHandler composeAuthenticationHandler() {
        return new AuthenticationHandler(redirectResponseWalk);
    }
}