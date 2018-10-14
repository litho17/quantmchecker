package SnapBuddy_1.com.cyberpointllc.stac.snapservice.persist;

import SnapBuddy_1.com.cyberpointllc.stac.snapservice.LocationService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Location;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import org.mapdb.Serializer;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

public class PersonSerializer extends Serializer<Person> {

    private final LocationService locationService;

    public PersonSerializer(LocationService locationService) {
        if (locationService == null) {
            throw new  IllegalArgumentException("LocationService may not be null");
        }
        this.locationService = locationService;
    }

    @Override
    public void serialize(DataOutput out, Person person) throws IOException {
        out.writeUTF(person.getIdentity());
        out.writeUTF(person.getName());
        out.writeUTF(person.getLocation().getIdentity());
        @Bound("+ person.photos person.friends") int i;
        @Inv("= (- friendIdentities it1) (- c40 c39)") Set<String> friendIdentities = new HashSet<>();
        @Iter("<= it1 person.friends") Iterator<String> it1 = person.friends.iterator();
        while (it1.hasNext()) {
            String s1;
            c39: s1 = it1.next();
            c40: friendIdentities.add(s1);
        }
        out.writeInt(friendIdentities.size());
        for (String friendIdentity : friendIdentities) {
            out.writeUTF(friendIdentity);
        }
        @Inv("= (- photoIdentities it2) (- c51 c50)") Set<String> photoIdentities = new HashSet<>();
        @Iter("<= it2 person.photos") Iterator<String> it2 = person.photos.iterator();
        while (it2.hasNext()) {
            String s2;
            c50: s2 = it2.next();
            c51: photoIdentities.add(s2);
        }
        out.writeInt(photoIdentities.size());
        for (String photoIdentity : photoIdentities) {
            out.writeUTF(photoIdentity);
        }
    }

    @Override
    public Person deserialize(DataInput in, int available) throws IOException {
        String identity = in.readUTF();
        String name = in.readUTF();
        String locationIdentity = in.readUTF();
        Location location = locationService.getLocation(locationIdentity);
        @Bound("+ in.numberOfFriends in.numberOfPhotos") int i;
        @Inv("= (+ friends numberOfFriends) (- c68 c69)") Set<String> friends = new  HashSet();
        @Iter("<= numberOfFriends in.numberOfFriends") int numberOfFriends = in.readInt();
        while (numberOfFriends > 0) {
            c68: friends.add(in.readUTF());
            c69: numberOfFriends = numberOfFriends - 1;
        }
        @Inv("= (+ photos numberOfPhotos) (- c74 c75)") Set<String> photos = new  HashSet();
        @Iter("<= numberOfPhotos in.numberOfPhotos") int numberOfPhotos = in.readInt();
        while (numberOfPhotos > 0) {
            c74: photos.add(in.readUTF());
            c75: numberOfPhotos = numberOfPhotos - 1;
        }
        return new  Person(identity, name, location, friends, photos);
    }
}
