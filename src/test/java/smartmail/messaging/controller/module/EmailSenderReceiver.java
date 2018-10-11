package smartmail.messaging.controller.module;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;
import smartmail.datamodel.SecureEmailAddress;
import smartmail.process.controller.module.PipelineController;
import smartmail.email.manager.module.addressbook.AddressBook;
import smartmail.datamodel.EmailAddress;
import smartmail.datamodel.EmailEvent;
import smartmail.datamodel.MailingList;
import smartmail.process.controller.module.seqfile.EmailParseException;
import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.URL;
import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;

import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.eclipse.jetty.http.HttpStatus;
import static smartmail.messaging.controller.module.RunSmartMail.clean;

public class EmailSenderReceiver extends HttpServlet {

    private final AddressBook abook;

    public EmailSenderReceiver() throws IOException {
        abook = AddressBook.getAddressBook();
    }

    /**
     * @see HttpServlet#doPost(HttpServletRequest request, HttpServletResponse
     * response)
     */
    protected synchronized void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {

        //TODO
        @InvUnk("Unknown API") StringBuffer requestURL = request.getRequestURL();
        URL url = new URL(requestURL.toString());
        System.out.println("path:" + url.getPath());

        String path = url.getPath();
        switch (path) {
            case "/email.cgi":
                doEmail(request, response);
                break;
            case "/mbox.cgi":
                getMBox(request, response);
                break;
            case "/address.cgi":
                getAddress(request, response);
                break;

            default:
                throw new IllegalArgumentException("ERROR:Unknown request type");
        }
    }

    private void getMBox(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {

        //STAC: Implements request handling functionality for reading from a mailbox
        String mbox = request.getParameter("mbox");
        if (mbox.length() > (25 + "@smartmail.com".length()) || !mbox.endsWith("@smartmail.com")) {
            mbox = mbox.toLowerCase();

            response.getWriter().println("ERROR: Invalid input");
            return;
        }

        //STAC:The AddressBook holds the pointer to the in-memory mailbox for a user
        EmailAddress mboxaddress = AddressBook.getAddressBook().lookupExistingAddress(mbox);

        EmailEvent fromMailBox = mboxaddress.getFromMailBox();

        //Check if any items in MBox
        if (fromMailBox == null) {
            response.getWriter().println("Sorry, Your MailBox is empty.");
        } else {

            //STAC: If there is an item, send it back to User
            EmailAddress source = fromMailBox.getSource();

            response.getWriter().println("From:" + source.getValue());
            response.getWriter().println("Subject:" + fromMailBox.getSubject());
            response.getWriter().println("Message:" + fromMailBox.getContent());
        }

    }

    private void getAddress(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {

        //STAC: Implements request handling functionality for getting public members of a mailing list
        // String list = request.getParameter("list");

        System.out.println("list:" + request.getParameter("list"));

        if (request.getParameter("list").length() > (25 + "@smartmail.com".length()) || !request.getParameter("list").endsWith("@smartmail.com")) {
            // list = list.toLowerCase();
            response.getWriter().println("ERROR: Invalid input");
            return;
        }

        EmailAddress lookupAddress = abook.lookupAddress(request.getParameter("list"));

        @Bound("* 2 ml.members") int i;
        @Inv("= (- addresses it2) (- c129 c128)") StringBuilder addresses = new StringBuilder();
        if (lookupAddress instanceof MailingList) {
            MailingList ml = (MailingList) lookupAddress;
            @Inv("= (- members it) (- c53 c51)") Set<EmailAddress> members = new TreeSet();
            @Iter("<= it ml.members") Iterator<EmailAddress> it = ml.members.iterator();

            while (it.hasNext()) {
                EmailAddress next;
                c51: next = it.next();
                boolean secretAddress = SecureEmailAddress.isSecretAddress(next);
                if (!secretAddress) {
                    c53: members.add(next);
                }
            }
            @Iter("<= it2 members") Iterator<EmailAddress> it2 = members.iterator();
            while (it2.hasNext()) {
                EmailAddress addr;
                c128: addr = it2.next();
                c129: addresses.append(addr.getValue() + ";");
            }

        }
        response.getWriter().println(addresses);

    }

    private void doEmail(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {

        //STAC: Implements request handling functionality for send and 'analyzing' an email
        //STAC: Vulnerabilty resides in this request
        String from = request.getParameter("from");
        System.out.println(from);
        from = from.toLowerCase();
        if (from.length() > (25 + "@smartmail.com".length()) || !from.endsWith("@smartmail.com")) {
            response.getWriter().println("ERROR: Invalid input");
            return;
        }
        
        String to = request.getParameter("to");
        
        
        if(to.length()>((25 + "@smartmail.com".length()+1)*10)){
            response.getWriter().println("ERROR: Invalid input, too long:" + to.length());
            return;        
        }
        String[] tos = to.split(";");
        //System.out.println(to + ":" +tos.length);
        //Split the 'To' field addresses
        
        @Inv("= (- toList j) (- c165 c166)") List<String> toList = new ArrayList<String>();
        for (@Iter("<= j tos") int j = 0; j < tos.length;) {
            c165: toList.add(tos[j]);
            c166: j = j + 1;
        }
        @Inv("= (- toListLower i) (- c172 c173)") List<String> toListLower = new ArrayList<String>();
        for (@Iter("<= i to") int i = 0; i < toList.size();) {
            String toitem = toList.get(i);
            if (toitem.length() > (25 + "@smartmail.com".length()) || !toitem.endsWith("@smartmail.com")) {

                response.getWriter().println("ERROR: Invalid input");
                return;
            }
            toitem = toitem.toLowerCase();
            c172: toListLower.add(toitem);
            c173: i = i + 1;
        }
        String subj = request.getParameter("subj");
        if (subj.length() > 125) {
            response.getWriter().println("ERROR: Invalid input");
            return;
        }
        String content = request.getParameter("content");
        if (content.length() > 250) {
            response.getWriter().println("ERROR: Invalid input");
            return;
        }

        long emailtime = System.currentTimeMillis();
        //Turn the request params into a Mime formatted string for parsing by a Mime parser
        String makeEmail = makeEmail(from, emailtime, toListLower, subj, content);

        //STAC: We write the email to disk -- later we delete it, when we have finished procesing
        String timeString = Long.toString(emailtime);
        clean("./mail");
        File email = new File("mail/" + timeString + ".mime");
        PrintWriter out = new PrintWriter(email);
        out.print(makeEmail);
        out.close();

        try {
            //STAC:Call the MapReducer
            PipelineController.main(null);

        } catch (@InvUnk("Extend library class") EmailParseException ex) {
            Logger.getLogger(EmailSenderReceiver.class.getName()).log(Level.SEVERE, null, ex);
        }
        if (email.exists()) {
            //STAC:Clean up the email, it was sent out and analyzed successfully
            email.delete();
        }

        response.getWriter().println("OK");

    }

    public String makeEmail(String from, long time, List<String> tofields, String subj, String content) {

        @Bound("+ tofields 5") int i;
        @Inv("= (- mimemessage it) (- (+ c223 c226 c231 c233 c234 c235) c230)") StringBuilder mimemessage = new StringBuilder();

        c223: mimemessage.append("MIME-Version: 1.0\n");
        Date date = new Date(time);
        //mimemessage.append("Date: " + date.toString()+"\n");
        c226: mimemessage.append("From: NAME <" + from + ">\n");
        @Iter("<= it tofields") Iterator<String> it = tofields.iterator();
        while (it.hasNext()) {
            String t;
            c230: t = it.next();
            c231: mimemessage.append("To: NAME <" + t + ">\n");
        }
        c233: mimemessage.append("Subject:" + subj + "\n");
        c234: mimemessage.append("Content-Type: text/plain\n\n");
        c235: mimemessage.append(content + "\n");

        return mimemessage.toString();
    }

}
