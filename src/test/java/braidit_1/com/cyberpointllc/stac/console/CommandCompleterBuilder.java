package braidit_1.com.cyberpointllc.stac.console;

public class CommandCompleterBuilder {
    private Display display;

    public CommandCompleterBuilder defineDisplay(Display display) {
        this.display = display;
        return this;
    }

    public CommandCompleter composeCommandCompleter() {
        return new CommandCompleter(display);
    }
}