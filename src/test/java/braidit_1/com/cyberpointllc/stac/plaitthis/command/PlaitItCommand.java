package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.console.Command;
import jline.console.completer.AggregateCompleter;
import jline.console.completer.ArgumentCompleter;
import jline.console.completer.Completer;
import jline.console.completer.FileNameCompleter;
import jline.console.completer.StringsCompleter;

public abstract class PlaitItCommand extends Command {
    protected PlaitItCommand(String command, String desc, String usage) {
        this(command, desc, usage, new AggregateCompleter(new ArgumentCompleter(new StringsCompleter(command), new FileNameCompleter())));
    }

    protected PlaitItCommand(String command, String desc, String usage, Completer completer) {
        super(command, desc, usage, completer);
    }
}
