package SnapBuddy_1.com.cyberpointllc.stac.snapservice;

import java.util.*;

import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Filter;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Invitation;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Location;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Photo;
import org.apache.commons.lang3.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.util.concurrent.TimeUnit;

public class SnapServiceImpl implements SnapService {

    private static final int LOCATION_CHANGE_LIMIT = 10;

    private final StorageService storageService;

    private final Map<String, Integer> locationChangeCounts;

    private long lastDay;

    public SnapServiceImpl(StorageService storageService) {
        if (storageService == null) {
            throw new  IllegalArgumentException("StorageService may not be null");
        }
        this.storageService = storageService;
        locationChangeCounts = new  HashMap();
        lastDay = TimeUnit.DAYS.convert(new  Date().getTime(), TimeUnit.MILLISECONDS);
    }

    @Override
    public String createPersonIdentity() {
        return storageService.createPersonIdentity();
    }

    @Override
    public Set<String> getPeople() {
        return storageService.getPeople();
    }

    @Override
    public Person getPerson(String identity) {
        return storageService.getPerson(identity);
    }

    @Override
    public Set<Person> getNeighbors(Person person) {
        if (person == null) {
            throw new  IllegalArgumentException("Person may not be null");
        }
        @Bound("storageService.getPeople") int i;
        @Inv("= (- neighbors it) (- c65 c62)") Set<Person> neighbors = new  HashSet();
        if (!Location.UNKNOWN.equals(person.getLocation())) {
            @Iter("<= it storageService.getPeople") Iterator<String> it = storageService.getPeople().iterator();
            while (it.hasNext()) {
                String identity;
                c62: identity = it.next();
                Person neighbor = getPerson(identity);
                if (!person.equals(neighbor) && person.getLocation().equals(neighbor.getLocation())) {
                    c65: neighbors.add(neighbor);
                }
            }
        }
        return neighbors;
    }

    @Override
    public boolean setName(Person person, String name) {
        if (person == null) {
            throw new  IllegalArgumentException("Person may not be null");
        }
        if (StringUtils.isBlank(name)) {
            return false;
        }
        Person newPerson = new  Person(person.getIdentity(), name, person.getLocation(), person.getFriends(), person.getPhotos());
        return storageService.updatePerson(newPerson);
    }

    @Override
    public boolean canUpdateLocation(Person person) {
        if (person == null) {
            throw new  IllegalArgumentException("Person may not be null");
        }
        String key = person.getIdentity();
        // First, determine if day crossing causes a reset
        long today = TimeUnit.DAYS.convert(new  Date().getTime(), TimeUnit.MILLISECONDS);
        if (today > lastDay) {
            lastDay = today;
            locationChangeCounts.clear();
        }
        // Ensure Person has an entry
        if (!locationChangeCounts.containsKey(key)) {
            locationChangeCounts.put(key, 0);
        }
        // Permit location changes if count limit is not reached
        return (locationChangeCounts.get(key) < LOCATION_CHANGE_LIMIT);
    }

    @Override
    public boolean setLocation(Person person, Location location) {
        if (person == null) {
            throw new  IllegalArgumentException("Person may not be null");
        }
        if (location == null) {
            location = Location.UNKNOWN;
        }
        if (person.getLocation().equals(location)) {
            return false;
        }
        if (!canUpdateLocation(person)) {
            throw new  IllegalArgumentException("Number of location requests per day has been exceeded");
        }
        // Increase the location change count; safe due to canUpdateLocation call
        locationChangeCounts.put(person.getIdentity(), (1 + locationChangeCounts.get(person.getIdentity())));
        Person newPerson = new  Person(person.getIdentity(), person.getName(), location, person.getFriends(), person.getPhotos());
        return storageService.updatePerson(newPerson);
    }

    @Override
    public boolean addFriends(Person person, Set<Person> friends) {
        if (person == null) {
            throw new  IllegalArgumentException("Person may not be null");
        }
        if (friends == null) {
            throw new  IllegalArgumentException("Set of friends may not be null");
        }
        if (friends.isEmpty()) {
            return false;
        }
        // Adding friends is bi-directional so first gather
        // up all of the friend identities to be added.
        @Bound("+ 1 friends") int i;
        @Inv("= (- identities it) (- (+ c151 c142) c145 c141)") Set<String> identities = new  HashSet();
        @Iter("<= it friends") Iterator<Person> it = friends.iterator();
        while (it.hasNext()) {
            Person friend;
            c141: friend = it.next();
            c142: identities.add(friend.getIdentity());
        }
        // Make sure this Person doesn't add their own identity as a friend
        c145: identities.remove(person.getIdentity());
        // Modify this person by adding these identities as friends
        boolean modified = modifyFriends(person, identities, true);
        // For the other direction, reset the set of identities
        // to now only hold this Person's identity
        identities.clear();
        c151: identities.add(person.getIdentity());
        // this Person to their collection of friends.
        for (Person friend : friends) {
            modified |= modifyFriends(friend, identities, true);
        }
        return modified;
    }

    @Override
    public boolean removeFriends(Person person, Set<Person> friends) {
        if (person == null) {
            throw new  IllegalArgumentException("Person may not be null");
        }
        if (friends == null) {
            throw new  IllegalArgumentException("Set of friends may not be null");
        }
        if (friends.isEmpty()) {
            return false;
        }
        // Removing friends is bi-directional so first gather
        // up all of the friend identities to be removed.
        @Bound("+ 1 friends")
        @Inv("= (- identities it) (- (+ c179 c186) c178)") Set<String> identities = new  HashSet();
        @Iter("<= it friends") Iterator<Person> it = friends.iterator();
        while (it.hasNext()) {
            Person friend;
            c178: friend = it.next();
            c179: identities.add(friend.getIdentity());
        }
        // Modify this person by removing these identities as friends
        boolean modified = modifyFriends(person, identities, false);
        // For the other direction, reset the set of identities
        // to now only hold this Person's identity
        identities.clear();
        c186: identities.add(person.getIdentity());
        // this Person from their collection of friends.
        for (Person friend : friends) {
            modified |= modifyFriends(friend, identities, false);
        }
        return modified;
    }

    @Override
    public boolean addPhoto(Person person, Photo photo) {
        return modifyPhoto(person, photo, true);
    }

    @Override
    public boolean removePhoto(Person person, Photo photo) {
        return modifyPhoto(person, photo, false);
    }

    @Override
    public Photo getPhoto(String identity) {
        return storageService.getPhoto(identity);
    }

    @Override
    public boolean setVisibility(Photo photo, boolean isPublic) {
        if (photo == null) {
            throw new  IllegalArgumentException("Photo may not be null");
        }
        boolean modified = isPublic != photo.isPublicPhoto();
        if (modified) {
            Photo newPhoto = new  Photo(photo.getPath(), isPublic, photo.getCaption(), photo.getLocation(), photo.getFilters());
            modified = storageService.updatePhoto(newPhoto);
        }
        return modified;
    }

    @Override
    public boolean setCaption(Photo photo, String caption) {
        if (photo == null) {
            throw new  IllegalArgumentException("Photo may not be null");
        }
        boolean modified = !(StringUtils.isBlank(caption) ? StringUtils.isBlank(photo.getCaption()) : caption.equals(photo.getCaption()));
        if (modified) {
            Photo newPhoto = new  Photo(photo.getPath(), photo.isPublicPhoto(), caption, photo.getLocation(), photo.getFilters());
            modified = storageService.updatePhoto(newPhoto);
        }
        return modified;
    }

    @Override
    public boolean setLocation(Photo photo, Location location) {
        if (photo == null) {
            throw new  IllegalArgumentException("Photo may not be null");
        }
        if (location == null) {
            location = Location.UNKNOWN;
        }
        boolean modified = !location.equals(photo.getLocation());
        if (modified) {
            Photo newPhoto = new  Photo(photo.getPath(), photo.isPublicPhoto(), photo.getCaption(), location, photo.getFilters());
            modified = storageService.updatePhoto(newPhoto);
        }
        return modified;
    }

    @Override
    public boolean addFilter(Photo photo, Filter filter) {
        return modifyFilter(photo, filter, true);
    }

    @Override
    public boolean removeFilter(Photo photo, Filter filter) {
        return modifyFilter(photo, filter, false);
    }

    @Override
    public boolean isPhotoVisible(Person person, Photo photo) {
        if (person == null) {
            throw new  IllegalArgumentException("Person may not be null");
        }
        if (photo == null) {
            throw new  IllegalArgumentException("Photo may not be null");
        }
        if (photo.isPublicPhoto()) {
            return true;
        } else if (person.ownsPhoto(photo)) {
            return true;
        }
        // Look at all of this Person's friends
        for (String friendId : person.getFriends()) {
            Person friend = getPerson(friendId);
            if ((friend != null) && friend.ownsPhoto(photo)) {
                return true;
            }
        }
        return false;
    }

    private boolean modifyFriends(Person person, Set<String> identities, boolean isAdding) {
        boolean modified;
        @Bound("person.getFriends")
        @Inv("= (- friends it) (- c292 c291)") Set<String> friends = new  HashSet();
        @Iter("<= it person.getFriends") Iterator<String> it = person.getFriends().iterator();
        while (it.hasNext()) {
            String p;
            c291: p = it.next();
            c292: friends.add(p);
        }
        if (isAdding) {
            modified = friends.addAll(identities);
        } else {
            modified = friends.removeAll(identities);
        }
        if (modified) {
            Person newPerson = new  Person(person.getIdentity(), person.getName(), person.getLocation(), friends, person.getPhotos());
            modified = storageService.updatePerson(newPerson);
        }
        return modified;
    }

    private boolean modifyPhoto(Person person, Photo photo, boolean isAdding) {
        if (person == null) {
            throw new  IllegalArgumentException("Person may not be null");
        }
        if (photo == null) {
            throw new  IllegalArgumentException("Photo may not be null");
        }
        boolean modified;
        if (isAdding) {
            modified = storageService.addPhoto(photo);
        } else {
            modified = storageService.deletePhoto(photo.getIdentity());
        }
        if (modified) {
            @Bound("+ 1 person.getPhotos") int i;
            @Inv("= (- photos it) (- (+ c325 c328) c324 c331)") Set<String> photos = new  HashSet();
            @Iter("<= it person.getPhotos") Iterator<String> it = person.getPhotos().iterator();
            while (it.hasNext()) {
                String p;
                c324: p = it.next();
                c325: photos.add(p);
            }
            if (isAdding) {
                c328: modified = photos.add(photo.getIdentity());
            } else {
                c331: modified = photos.remove(photo.getIdentity());
            }
            if (modified) {
                Person newPerson = new  Person(person.getIdentity(), person.getName(), person.getLocation(), person.getFriends(), photos);
                modified = storageService.updatePerson(newPerson);
            }
        }
        return modified;
    }

    private boolean modifyFilter(Photo photo, Filter filter, boolean isAdding) {
        if (photo == null) {
            throw new  IllegalArgumentException("Photo may not be null");
        }
        boolean modified = false;
        if (filter != null) {
            @Bound("+ 1 photo.getFilters") int i;
            @Inv("= (- filters it) (- (+ c352 c355) c351 c357)") List<Filter> filters = new  ArrayList();
            @Iter("<= it photo.getFilters") Iterator<Filter> it = photo.getFilters().iterator();
            while (it.hasNext()) {
                Filter f;
                c351: f = it.next();
                c352: filters.add(f);
            }
            if (isAdding) {
                c355: modified = filters.add(filter);
            } else {
                c357: modified = filters.remove(filter);
            }
            if (modified) {
                Photo newPhoto = new  Photo(photo.getPath(), photo.isPublicPhoto(), photo.getCaption(), photo.getLocation(), filters);
                modified = storageService.updatePhoto(newPhoto);
            }
        }
        return modified;
    }

    @Override
    public Set<Person> getInvitations(Person person) {
        if (person == null) {
            throw new  IllegalArgumentException("Person may not be null");
        }
        @Bound("storageService.getInvitations") int i;
        @Inv("= (- people it) (- c379 c377)") Set<Person> people = new  HashSet();
        @Iter("<= it storageService.getInvitations") Iterator<Invitation> it = storageService.getInvitations().iterator();
        while (it.hasNext()) {
            Invitation invitation;
            c377: invitation = it.next();
            if (person.getIdentity().equals(invitation.getInviteFromIdentity())) {
                c379: people.add(getPerson(invitation.getInviteToIdentity()));
            } else if (person.getIdentity().equals(invitation.getInviteToIdentity())) {
                getInvitationsHelper(invitation, people);
            }
        }
        return people;
    }

    @Override
    public Set<Person> getInvitationsTo(Person person) {
        if (person == null) {
            throw new  IllegalArgumentException("Person may not be null");
        }
        @Bound("storageService.getInvitations") int i;
        @Inv("= (- people it) (- c401 c399)") Set<Person> people = new  HashSet();
        @Iter("<= it storageService.getInvitations") Iterator<Invitation> it = storageService.getInvitations().iterator();
        while (it.hasNext()) {
            Invitation invitation;
            c399: invitation = it.next();
            if (person.getIdentity().equals(invitation.getInviteToIdentity())) {
                c401: people.add(getPerson(invitation.getInviteFromIdentity()));
            }
        }
        return people;
    }

    @Override
    public boolean sendInvitation(Person sender, Person receiver) {
        if (sender == null) {
            throw new  IllegalArgumentException("Sending Person may not be null");
        }
        if (receiver == null) {
            throw new  IllegalArgumentException("Receiving Person may not be null");
        }
        boolean added = false;
        // First, check that a reverse invitation doesn't already exist
        Invitation reverseInvitation = new  Invitation(receiver.getIdentity(), sender.getIdentity());
        if (!storageService.getInvitations().contains(reverseInvitation)) {
            // Reverse invitation does not already exist; add a new one
            added = storageService.addInvitation(new  Invitation(sender.getIdentity(), receiver.getIdentity()));
        }
        return added;
    }

    @Override
    public boolean acceptInvitation(Person sender, Person receiver) {
        if (sender == null) {
            throw new  IllegalArgumentException("Sending Person may not be null");
        }
        if (receiver == null) {
            throw new  IllegalArgumentException("Receiving Person may not be null");
        }
        Invitation matchingInvitation = new  Invitation(sender.getIdentity(), receiver.getIdentity());
        if (!storageService.getInvitations().contains(matchingInvitation)) {
            // No match; try the reverse invitation
            matchingInvitation = new  Invitation(receiver.getIdentity(), sender.getIdentity());
            if (!storageService.getInvitations().contains(matchingInvitation)) {
                // No match either; no invitation to accept
                matchingInvitation = null;
            }
        }
        boolean response = false;
        if (matchingInvitation != null) {
            storageService.deleteInvitation(matchingInvitation);
            response = addFriends(sender, Collections.singleton(receiver));
        }
        return response;
    }

    @Override
    public boolean rejectInvitation(Person sender, Person receiver) {
        if (sender == null) {
            throw new  IllegalArgumentException("Sending Person may not be null");
        }
        if (receiver == null) {
            throw new  IllegalArgumentException("Receiving Person may not be null");
        }
        Invitation matchingInvitation = new  Invitation(sender.getIdentity(), receiver.getIdentity());
        if (!storageService.getInvitations().contains(matchingInvitation)) {
            // No match; try the reverse invitation
            matchingInvitation = new  Invitation(receiver.getIdentity(), sender.getIdentity());
            if (!storageService.getInvitations().contains(matchingInvitation)) {
                // No match either; no invitation to accept
                matchingInvitation = null;
            }
        }
        boolean response = false;
        if (matchingInvitation != null) {
            response = storageService.deleteInvitation(matchingInvitation);
        }
        return response;
    }

    private void getInvitationsHelper(Invitation invitation, Set<Person> people) {
        people.add(getPerson(invitation.getInviteFromIdentity()));
    }
}
