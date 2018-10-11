/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package smartmail.email.manager.module.parser.email.xtra;

/**
 *
 * @author burkep
 */
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import smartmail.datamodel.EmailEvent;
import smartmail.process.controller.module.seqfile.EmailParseException;
import java.io.File;
import java.util.ArrayList;
import java.util.List;

//TODO: TO eMAILpARSER
public class EmailParserUtil {

    public EmailDirHandler email;

    public void init(final File file) {
        email = new EmailDirHandler();
        email.openOffline(file.getAbsolutePath());

    }

    public void close() {
        email.close();
    }

}
