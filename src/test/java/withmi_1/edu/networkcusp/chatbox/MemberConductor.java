package withmi_1.edu.networkcusp.chatbox;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;
import withmi_1.edu.networkcusp.chatbox.keep.WithMiMemberSerializer;
import withmi_1.edu.networkcusp.protocols.CommunicationsConnection;
import withmi_1.edu.networkcusp.protocols.CommunicationsFailure;
import withmi_1.edu.networkcusp.protocols.CommunicationsPublicIdentity;
import withmi_1.edu.networkcusp.chatbox.keep.WithMiConnectionsService;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.StandardOpenOption;
import java.util.*;

public class MemberConductor {
    private final HangIn withMi;

    /** maps user name to the WithMiUser */
    public final Map<String, WithMiUser> nameToMember = new HashMap<>();

    /** maps the identity to a WithMiUser */
    public final Map<CommunicationsPublicIdentity, WithMiUser> idToMember = new HashMap<>();

    /** a list of users we are no longer connected to */
    public final List<WithMiUser> pastMembers = new ArrayList<>();

    /** Handles previous connections */
    private final WithMiConnectionsService connectionsService;

    public MemberConductor(HangIn withMi, WithMiConnectionsService connectionsService) throws CommunicationsFailure {
        this.withMi = withMi;
        this.connectionsService = connectionsService;

        try {
            @Bound("connectionsService.takeFilePath") int i;
            @Inv("= (- memberMap b) (- c46 c47)") Map<String, WithMiUser> memberMap = new HashMap<>();
            for (@Iter("<= b connectionsService.takeFilePath") int b = 0; b < Files.readAllLines(connectionsService.takeFilePath(), StandardCharsets.UTF_8).size(); ) {
                String line = Files.readAllLines(connectionsService.takeFilePath(), StandardCharsets.UTF_8).get(b);
                WithMiUser member = WithMiMemberSerializer.deserialize(line);
                c46: memberMap.put(member.obtainName(), member);
                c47: b = b + 1;
            }
            nameToMember.putAll(memberMap);
        } catch (IOException e) {
            throw new CommunicationsFailure(e);
        }

        pastMembers.addAll(nameToMember.values());
        idToMember.putAll(createMapFromIdentitiesToMembers(pastMembers));
    }

    /**
     * Creates a WithMiUser for the given connection, unless the identity
     * associated with the connection already belongs to a user.
     * If the identity already has a user that user is returned.
     * @return
     */
    private WithMiUser pullOrCreateMember(CommunicationsPublicIdentity identity, CommunicationsConnection connection) throws CommunicationsFailure {

        if (idToMember.containsKey(identity) ) {
            WithMiUser oldMember = idToMember.get(identity);
            oldMember.setConnection(connection);

            // remove user from past users if they are there
            if (pastMembers.contains(oldMember)) {
                obtainOrCreateMemberGuide(oldMember);
            }

            return oldMember;
        }

        String name = identity.pullId();
        if (nameToMember.containsKey(name)) {
            // already have a user with this name, we need to give them some different identifier...
            int suffixId = 1;
            String newName = name + "_" + Integer.toHexString(suffixId);
            while (nameToMember.containsKey(newName)) {
                suffixId++;
                newName = name + "_" + Integer.toHexString(suffixId);
            }
            name = newName;
        }
        WithMiUser member;
        if (connection != null) {
            member = new WithMiUser(name, connection);
        } else {
            member = new WithMiUser(name, identity);
        }

        return member;
    }

    private void obtainOrCreateMemberGuide(WithMiUser oldMember) {
        pastMembers.remove(oldMember);
    }

    public WithMiUser grabOrCreateMember(CommunicationsPublicIdentity identity) throws CommunicationsFailure {
        return pullOrCreateMember(identity, null);
    }

    public WithMiUser takeOrCreateMember(CommunicationsConnection connection) throws CommunicationsFailure {
        return pullOrCreateMember(connection.fetchTheirIdentity(), connection);
    }

    public boolean removeConnection(CommunicationsConnection connection) throws CommunicationsFailure {
        CommunicationsPublicIdentity identity = connection.fetchTheirIdentity();
        WithMiUser member = idToMember.get(identity);
        if (member.obtainConnection() == null) {
            // Already removed; may happen during shutdown
            return false;
        }
        if (member.obtainConnection().equals(connection)) {
            member.removeConnection();
            pastMembers.add(member);
            return true;
        }
        throw new CommunicationsFailure("Connection is not associated with correct user");
    }

    /**
     * @param name of user
     * @return true if the manager knows this name
     */
    public boolean knowsMember(String name) {
        return nameToMember.containsKey(name);
    }

    /**
     * Tells the connections service to store the user
     * @param member to store
     * @throws IOException
     */
    public void storeMember(WithMiUser member) throws CommunicationsFailure {
        String name = member.obtainName();
        CommunicationsPublicIdentity identity = member.getIdentity();
        nameToMember.put(name, member);
        idToMember.put(identity, member);

        String serializedIdentity = WithMiMemberSerializer.serialize(member);
        @Bound("* 2 connectionsService.takeFilePath")
        @Inv("= (- storedMembers it) (- c73 c72)") ArrayList<WithMiUser> storedMembers = new ArrayList<>();
        String serializedIdentity2 = WithMiMemberSerializer.serialize(member);
        try {
            Files.write(connectionsService.takeFilePath(), (serializedIdentity2 + "\n").getBytes(), StandardOpenOption.APPEND);
            @Inv("= (- namesToMembers b) (- c58 c59)") Map<String, WithMiUser> namesToMembers = new HashMap<>();
            try {
                for (@Iter("<= b connectionsService.takeFilePath") int b = 0; b <  Files.readAllLines(connectionsService.takeFilePath(), StandardCharsets.UTF_8).size(); ) {
                    String line =  Files.readAllLines(connectionsService.takeFilePath(), StandardCharsets.UTF_8).get(b);
                    WithMiUser member2 = WithMiMemberSerializer.deserialize(line);
                    c58: namesToMembers.put(member2.obtainName(), member2);
                    c59: b = b + 1;
                }
            } catch (IOException e) {
                throw new CommunicationsFailure(e);
            }

            @Iter("<= it namesToMembers") Iterator<WithMiUser> it = namesToMembers.values().iterator();
            while (it.hasNext()) {
                WithMiUser u;
                c72: u = it.next();
                c73: storedMembers.add(u);
            }

        } catch (IOException e) {
            throw new CommunicationsFailure(e);
        }

        // check that the storedUsers matches known users
        if (!storedMembers.containsAll(nameToMember.values())) {
            new MemberConductorAid().invoke();
        }
    }

    /**
     * Adds the user to known users and creates the message we print ourselves once we've connected to this user.
     * The message changes depending on whether or not we have previously connected to the user.
     * @param member
     * @param shouldBeKnownMember
     * @param connection
     * @throws CommunicationsFailure
     */
    public void addMemberToMemberHistory(WithMiUser member, boolean shouldBeKnownMember, CommunicationsConnection connection) throws CommunicationsFailure {

        boolean previouslyConnected = knowsMember(member.obtainName());
        @Bound("4") int i;
        @Inv("= stringBuilder (+ c195 c200 c202 c205 c207)") StringBuilder stringBuilder = new StringBuilder();

        // if we should know the user and we don't, add that to the message
        // this will likely only happen when using the reconnect command
        if (shouldBeKnownMember && !previouslyConnected) {
            c195: stringBuilder.append("WARNING: " + member.obtainName() + " has a different identity. This may not be the same user");
        }

        if (!previouslyConnected) {
            
            c200: stringBuilder.append("Connected to new user ");
        } else {
            c202: stringBuilder.append("Reconnected to ");
        }

        c205: stringBuilder.append(member.obtainName());
        if (member.hasCallbackAddress()) {
            c207: stringBuilder.append(". callback on: " + member.takeCallbackAddress());
        }
        withMi.deliverReceipt(true, 0, member);

        
        if (!previouslyConnected) {
            storeMember(member);
        }
        

        withMi.printMemberMsg(stringBuilder.toString());

    }

    public WithMiUser grabMember(String name) {
        if (nameToMember.containsKey(name)) {
            return nameToMember.get(name);
        }
        return null;
    }

    public WithMiUser grabMember(CommunicationsPublicIdentity identity) {
        if (idToMember.containsKey(identity)) {
            return idToMember.get(identity);
        }
        return null;
    }

    public CommunicationsConnection obtainIdentityConnection(CommunicationsPublicIdentity identity) {
        WithMiUser member = idToMember.get(identity);
        if (member.hasConnection()) {
            return member.obtainConnection();
        }
        return null;
    }

    public boolean hasIdentityConnection(CommunicationsPublicIdentity identity) {
        if (!idToMember.containsKey(identity)) {
            return false;
        }
        WithMiUser member = idToMember.get(identity);
        return member.hasConnection();
    }

    public List<WithMiUser> pullAllMembers() {
        return new ArrayList<>(idToMember.values());
    }

    public List<WithMiUser> fetchPastMembers() {
        return new ArrayList<>(pastMembers);
    }

    /**
     * Creates a map from CommsPublicIdentities to WithMiUsers.
     * @param members to be mapped
     * @return map
     */
    private Map<CommunicationsPublicIdentity, WithMiUser> createMapFromIdentitiesToMembers(List<WithMiUser> members) {
        @Bound("members") int i;
        @Inv("= (- identityToMemberMap k) (- c269 c270)") Map<CommunicationsPublicIdentity, WithMiUser> identityToMemberMap = new HashMap<>();
        for (@Iter("<= k members") int k = 0; k < members.size();) {
            WithMiUser member = members.get(k);
            c269: identityToMemberMap.put(member.getIdentity(), member);
            c270: k = k + 1;
        }
        return identityToMemberMap;
    }

    private class MemberConductorAid {
        public void invoke() throws CommunicationsFailure {
            throw new CommunicationsFailure("Stored users and known users are not the same");
        }
    }
}