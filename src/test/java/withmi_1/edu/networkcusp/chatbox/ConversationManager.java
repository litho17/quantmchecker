package withmi_1.edu.networkcusp.chatbox;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;
import withmi_1.edu.networkcusp.protocols.Comms;
import withmi_1.edu.networkcusp.protocols.CommunicationsFailure;
import withmi_1.edu.networkcusp.protocols.CommunicationsPublicIdentity;
import withmi_1.edu.networkcusp.protocols.SerializerUtil;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.UUID;

/**
 * Manages the user's chats
 * STAC_ALT_NAMES: ConversationManager
 */
public class ConversationManager {
    private static final String DEFAULT_CHAT_NAME = "myFirstChat";

    /**
     * maps chat name to chat
     */
    public final Map<String, WithMiChat> nameToDiscussion = new HashMap<>();

    /**
     * maps unique id to chat name
     */
    private final Map<String, String> idToName = new HashMap<>();

    private final Map<WithMiUser, List<WithMiChat>> memberToDiscussions = new HashMap<>();

    private final HangIn withMi;

    /**
     * the current chat
     */
    public WithMiChat currentDiscussion;

    public ConversationManager(HangIn withMi) {
        this.withMi = withMi;
        createDiscussion(DEFAULT_CHAT_NAME);
        currentDiscussion = obtainDiscussion(DEFAULT_CHAT_NAME);
    }

    /**
     * Returns a chat associated with the given name
     *
     * @param name of chat
     * @return chat
     */
    public WithMiChat obtainDiscussion(String name) {
        return nameToDiscussion.get(name);
    }

    /**
     * Creates and returns a new group chat with the given name.
     * If a group chat already has that name, returns false.
     *
     * @param discussionName
     * @return true if chat is successfully created
     */
    public boolean createDiscussion(String discussionName) {
        if (nameToDiscussion.containsKey(discussionName)) {
            return createDiscussionGuide();
        }
        String uniqueId = UUID.randomUUID().toString();
        return createDiscussion(discussionName, uniqueId);
    }

    private boolean createDiscussionGuide() {
        withMi.printMemberMsg("A chat with this name already exists");
        return false;
    }

    /**
     * Creates a group chat with given name and the given uniqueId.
     * This method is used when being added to a group chat that already has a unique id.
     *
     * @param discussionName
     * @param uniqueId
     * @return true if chat is successfully created
     */
    private boolean createDiscussion(String discussionName, String uniqueId) {
        if (nameToDiscussion.containsKey(discussionName)) {
            // already have a user with this name, we need to give them some different identifier...
            int suffixId = 1;
            String newName = discussionName + "_" + Integer.toHexString(suffixId);
            while (nameToDiscussion.containsKey(newName)) {
                suffixId++;
                newName = discussionName + "_" + Integer.toHexString(suffixId);
            }
            discussionName = newName;
        }

        WithMiChat groupDiscussion = new WithMiChat(withMi, discussionName, uniqueId);
        nameToDiscussion.put(discussionName, groupDiscussion);
        idToName.put(groupDiscussion.getUniqueId(), discussionName);
        currentDiscussion = groupDiscussion;
        return true;
    }

    /**
     * @param name of chat
     * @return true if we are currently in the chat with the given name
     */
    public boolean inDiscussion(String name) {
        return nameToDiscussion.containsKey(name);
    }

    /**
     * @param uniqueId of chat
     * @return name of chat associated with the given id
     */
    public String pullDiscussionNameFromUniqueId(String uniqueId) {
        return idToName.get(uniqueId);
    }

    /**
     * @return names of all the chats we're in
     */
    public List<String> pullAllDiscussionNames() {
        return new ArrayList<>(nameToDiscussion.keySet());
    }

    /**
     * Receives a chat message and decides where to put it. If we are currently in the chat associated with
     * the message, this prints the message. If we are in a different chat, this stores the unread message for when we
     * switch to that chat.
     *
     * @param sender   of the message
     * @param discussionMsg
     * @param uniqueId of chat associated with the message
     */
    public void handleDiscussionMessage(String sender, Chat.ChatMsg discussionMsg, String uniqueId) {
        WithMiChat discussion = obtainDiscussion(pullDiscussionNameFromUniqueId(uniqueId));
        String text = discussionMsg.getTextMsg();
        String readableMsg = sender + ": " + text;
        if (discussion.equals(currentDiscussion)) {
            withMi.printMemberMsg(readableMsg);
        } else {
            discussion.storeUnreadMessage(readableMsg);
        }
    }

    /**
     * Receives a chat state message, which indicates that the given chat has changed in some way. This message
     * received when a user has been added to a chat we are already in, or we have been added to a previously unknown chat.
     *
     * @param msg
     * @param discussionId   of the new chat
     * @param discussionName suggested by the user adding us to the chat
     * @throws CommunicationsFailure
     */
   public void handleDiscussionStateMessage(Chat.ChatStateMsg msg, String discussionId, String discussionName) throws CommunicationsFailure {
       // if we don't know about this chat, it means we are being added to a new chat
       // create this chat
       if (pullDiscussionNameFromUniqueId(discussionId) == null) {
           createDiscussion(discussionName, discussionId);
           withMi.printMemberMsg("Added new chat " + pullDiscussionNameFromUniqueId(discussionId));
       }

       WithMiChat discussion = obtainDiscussion(pullDiscussionNameFromUniqueId(discussionId));

       // get the list of user identities in this chat
       @Bound("msg.publicId_") int j;
       @Inv("= (- membersInDiscussion a) (- c176 c178)") List<CommunicationsPublicIdentity> membersInDiscussion = new ArrayList<>();
       for (@Iter("<= a msg.publicId_") int a = 0; a < msg.publicId_.size();) {
           Comms.Identity publicId = msg.publicId_.get(a);
           CommunicationsPublicIdentity identity = SerializerUtil.deserializeIdentity(publicId);
           // Users with the null identity shouldn't be added to this chat
           if (!identity.equals(WithMiChat.NULL_IDENTITY)) {
               c176: membersInDiscussion.add(identity);
           }
           c178: a = a + 1;
       }

       // only connect to the identities before ours in the list
       boolean beforeMe = true;
       for (int k = 0; k < membersInDiscussion.size(); k++) {
           CommunicationsPublicIdentity identity = membersInDiscussion.get(k);
           if (identity.equals(withMi.takeMyIdentity())) {
               beforeMe = false;
               continue;
           }

           if (beforeMe && !withMi.isConnectedTo(identity)) {
               // if we don't know about this identity and it's before us in the list,
               //  connect
               handleDiscussionStateMessageUtility(identity);
           }


           // get the WithMiUser with this identity or create one without a connection
           WithMiUser member;
           if (withMi.isConnectedTo(identity)) {
               member = withMi.grabMember(identity);
           } else {
               member = withMi.createAndStoreMember(identity);
           }

           // if it isn't in the chat, add it
           if (!discussion.containsMember(member)) {
               handleDiscussionStateMessageTarget(discussion, member);
           }
       }
   }

    private void handleDiscussionStateMessageTarget(WithMiChat discussion, WithMiUser member) {
        withMi.printMemberMsg("Adding " + member.obtainName() + " to " + discussion.grabName());
        addMemberToDiscussion(discussion, member);
    }

    private void handleDiscussionStateMessageUtility(CommunicationsPublicIdentity identity) throws CommunicationsFailure {
        withMi.connect(identity.obtainCallbackAddress(), false);
    }

    public void addMemberToDiscussion(WithMiChat discussion, WithMiUser member) {
        discussion.addMember(member);

        // update the userToChats list
        if (memberToDiscussions.containsKey(member)) {
            memberToDiscussions.get(member).add(discussion);
        } else {
            List<WithMiChat> discussions = new ArrayList<>();
            discussions.add(discussion);
            memberToDiscussions.put(member, discussions);
        }
    }

    public void removeMemberFromAllDiscussions(WithMiUser member) {
        withMi.printMemberMsg("Removing " + member.obtainName() + " from all chats");
        @InvUnk("Nested lists") List<WithMiChat> discussions = memberToDiscussions.get(member);
        if (discussions != null) { // Can be null if user has not been assigned to a chat yet
            for (int p = 0; p < discussions.size(); p++) {
                @InvUnk("Nested lists") WithMiChat discussion;
                discussion = discussions.get(p);
                discussion.removeMember(member);
            }
        }
    }

    public WithMiChat fetchCurrentDiscussion() {
        return currentDiscussion;
    }

    public boolean switchToDiscussion(String name) {
        if (inDiscussion(name)) {
            currentDiscussion = nameToDiscussion.get(name);
            return true;
        }
        return false;
    }
}
