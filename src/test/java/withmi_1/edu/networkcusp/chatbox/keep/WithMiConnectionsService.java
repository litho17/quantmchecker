package withmi_1.edu.networkcusp.chatbox.keep;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;
import withmi_1.edu.networkcusp.protocols.CommunicationsFailure;
import withmi_1.edu.networkcusp.chatbox.WithMiUser;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.*;

/**
 * Handles information about users and previous connections.
 * Reads in user information from a file and writes information to that file.
 */
public class WithMiConnectionsService {

    /** name of file that stores the information of users we've connected to */
    private static final String FILE_NAME = "previous_users.txt";

    private final String dataDir;

    public WithMiConnectionsService(String dataDir) throws IOException {
        this.dataDir = dataDir;
        File fileOfMembers = takeFilePath().toFile();
        if (!fileOfMembers.exists()) {
            new WithMiConnectionsServiceSupervisor(fileOfMembers).invoke();
        }
    }

    /**
     * Returns the Path of our storage file. The file contains the names and public identities
     * of users that we've previous connected to.
     * @return
     */
    public Path takeFilePath() {
        return Paths.get(dataDir, FILE_NAME);
    }


    private class WithMiConnectionsServiceSupervisor {
        private File fileOfMembers;

        public WithMiConnectionsServiceSupervisor(File fileOfMembers) {
            this.fileOfMembers = fileOfMembers;
        }

        public void invoke() throws IOException {
            fileOfMembers.getParentFile().mkdir();
            fileOfMembers.createNewFile();
        }
    }
}
