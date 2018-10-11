/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package smartmail.datamodel;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.io.IOException;
import java.util.Iterator;
import java.util.Set;
import java.util.TreeSet;

/**
 *
 * @author user
 */
public class MailingList extends EmailAddress {

    public Set<EmailAddress> members;

    public MailingList(int uid) {
        super(uid);
        members = new TreeSet();
    }

    public Set<EmailAddress> getMembers() {
        return members;
    }

    public void setMember(Set<EmailAddress> members) {
        this.members = members;
    }

    public void addMember(EmailAddress member) {

        this.members.add(member);

    }

    public Set<EmailAddress> getPublicMembers() throws IOException {
        @Bound("members") int i;
        @Inv("= (- pmembers it) (- c53 c51)") Set<EmailAddress> pmembers = new TreeSet();
        @Iter("<= it members") Iterator<EmailAddress> it = members.iterator();

        while (it.hasNext()) {
            EmailAddress next;
            c51: next = it.next();
            boolean secretAddress = SecureEmailAddress.isSecretAddress(next);
            if (!secretAddress) {
                c53: pmembers.add(next);
            }
        }

        return pmembers;
    }

}
