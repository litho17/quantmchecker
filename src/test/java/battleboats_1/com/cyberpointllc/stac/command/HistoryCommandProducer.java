package battleboats_1.com.cyberpointllc.stac.command;

public class HistoryCommandProducer {
    private Console console;

    public HistoryCommandProducer assignConsole(Console console) {
        this.console = console;
        return this;
    }

    public HistoryCommand makeHistoryCommand() {
        return new HistoryCommand(console);
    }
}