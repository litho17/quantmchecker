package braidit_1.com.cyberpointllc.stac.console;

public class ScriptCommandBuilder {
    private Display display;

    public ScriptCommandBuilder defineDisplay(Display display) {
        this.display = display;
        return this;
    }

    public ScriptCommand composeScriptCommand() {
        return new ScriptCommand(display);
    }
}