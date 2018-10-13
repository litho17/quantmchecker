package SnapBuddy_1.com.cyberpointllc.stac.host;

import SnapBuddy_1.com.cyberpointllc.stac.common.DESHelper;
import java.util.HashMap;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.persist.MapDBStorageService;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.User;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.LocationService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Filter;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.FilterFactory;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Location;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Photo;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Loads SnapBuddy maps from provided input streams.
 */
public class SnapBuddyLoader {

    private static final String PEOPLE_RESOURCE = "initialpersons.csv";

    private static final String PHOTOS_RESOURCE = "initialphotos.csv";

    private static final String USERS_RESOURCE = "initialusers.csv";

    public static void populate(MapDBStorageService storageService, LocationService locationService, String passwordKey) throws IOException {
        try (InputStream inputStream = SnapBuddyLoader.class.getResourceAsStream(PHOTOS_RESOURCE)) {
            System.out.format("Loaded %d photos%n", SnapBuddyLoader.getPhotos(inputStream, locationService).size());
            for (Photo photo : SnapBuddyLoader.getPhotos(inputStream, locationService).values()) {
                storageService.addPhoto(photo);
            }
        }
        try (InputStream inputStream = SnapBuddyLoader.class.getResourceAsStream(PEOPLE_RESOURCE)) {
            System.out.format("Loaded %d people%n", SnapBuddyLoader.getPeople(inputStream, locationService).size());
            for (Person person : SnapBuddyLoader.getPeople(inputStream, locationService).values()) {
                storageService.addPerson(person);
            }
        }
        try (InputStream inputStream = SnapBuddyLoader.class.getResourceAsStream(USERS_RESOURCE)) {
            System.out.format("Loaded %d users%n", SnapBuddyLoader.getUsers(inputStream, passwordKey).size());
            for (User user : SnapBuddyLoader.getUsers(inputStream, passwordKey).values()) {
                storageService.addUser(user);
            }
        }
    }

    private static Map<String, Photo> getPhotos(InputStream inputStream, LocationService locationService) {
        @Bound("+ line.parts_4 inputStream") int KK;
        @Inv("= (- photos reader) (- c81 c83 c64)") Map<String, Photo> photos = new  HashMap();
        try (@Iter("<= reader inputStream") BufferedReader reader = new  BufferedReader(new  InputStreamReader(inputStream))) {
            String line;
            c64: line = reader.readLine();
            while (line != null) {
                String[] parts = line.split(",", 5);
                String path = parts[0];
                boolean isPublic = parts[1].isEmpty() ? true : Boolean.valueOf(parts[1]);
                Location location = parts[2].isEmpty() ? Location.UNKNOWN : locationService.getLocation(parts[2]);
                String caption = parts[3];
                @Inv("= (- filters i) (- c76 c78)") List<Filter> filters = new  ArrayList();
                String[] ary = parts[4].split(";");
                for (@Iter("<= i line.parts_4") int i = 0; i < ary.length; ) {
                    Filter filter = FilterFactory.getFilter(ary[i]);
                    if (filter != null) {
                        c76: filters.add(filter);
                    }
                    c78: i = i + 1;
                }
                if (!path.isEmpty()) {
                    c81: photos.put(path, new  Photo(path, isPublic, caption, location, filters));
                }
                c83: line = reader.readLine();
            }
        } catch (IOException e) {
            throw new  IllegalArgumentException("Trouble parsing Photo resources", e);
        }
        return photos;
    }

    private static Map<String, Person> getPeople(InputStream inputStream, LocationService locationService) {
        @Bound("+ line.parts_3 line.parts_4 inputStream") int k;
        @Inv("= (- people reader) (-c115 c117 c96)") Map<String, Person> people = new  HashMap();
        try (@Iter("<= reader inputStream") BufferedReader reader = new  BufferedReader(new  InputStreamReader(inputStream))) {
            String line;
            c96: line = reader.readLine();
            while (line != null) {
                String[] parts = line.split(",", 5);
                String identity = parts[0];
                String name = parts[1].isEmpty() ? "Unknown Name" : parts[1];
                Location location = parts[2].isEmpty() ? Location.UNKNOWN : locationService.getLocation(parts[2]);
                @Inv("= (- photoIds i) (- c106 c108)") Set<String> photoIds = new  HashSet();
                String[] ary1 = parts[3].split(";");
                for (@Iter("<= i line.parts_3") int i = 0; i < ary1.length;) {
                    if (!ary1[i].isEmpty()) {
                        c106: photoIds.add(ary1[i]);
                    }
                    c108: i = i + 1;
                }
                @Inv("= (- friendIds j) (- c114 c116)") Set<String> friendIds = new  HashSet();
                String[] ary2 = parts[4].split(";");
                for (@Iter("<= j line.parts_4") int j = 0; j < ary2.length;) {
                    if (!ary2[j].isEmpty()) {
                        c114: friendIds.add(ary2[j]);
                    }
                    c116: j = j + 1;
                }
                if (!identity.isEmpty()) {
                    c115: people.put(identity, new  Person(identity, name, location, friendIds, photoIds));
                }
                c117: line = reader.readLine();
            }
        } catch (IOException e) {
            throw new  IllegalArgumentException("Trouble parsing Person resources", e);
        }
        return people;
    }

    private static Map<String, User> getUsers(InputStream inputStream, String passwordKey) {
        @Bound("inputStream") int i;
        @Inv("= (- users reader) (- c148 c134 c150)") Map<String, User> users = new  HashMap();
        try (@Iter("<= reader inputStream") BufferedReader reader = new  BufferedReader(new  InputStreamReader(inputStream))) {
            String line;
            c134: line = reader.readLine();
            while (line != null) {
                String[] parts = line.split(",", 3);
                String identity = parts[0];
                String username = parts[1];
                String password = parts[2];
                if (password.length() < User.MIN_PASSWORD_LENGTH) {
                    throw new  IllegalArgumentException("Password may not be less than " + User.MIN_PASSWORD_LENGTH + " characters");
                }
                if (password.length() > User.MAX_PASSWORD_LENGTH) {
                    throw new  IllegalArgumentException("Password may not be more than " + User.MAX_PASSWORD_LENGTH + " characters");
                }
                String encryptedPw = DESHelper.getEncryptedString(password, passwordKey);
                if (!identity.isEmpty() && !username.isEmpty() && !encryptedPw.isEmpty()) {
                    c148: users.put(identity, new  User(identity, username, encryptedPw));
                }
                c150: line = reader.readLine();
            }
        } catch (IOException e) {
            throw new  IllegalArgumentException("Trouble parsing User resources", e);
        }
        return users;
    }
}
