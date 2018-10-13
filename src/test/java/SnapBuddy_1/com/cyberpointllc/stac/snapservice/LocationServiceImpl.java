package SnapBuddy_1.com.cyberpointllc.stac.snapservice;

import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.AccessPoint;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Location;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

public class LocationServiceImpl implements LocationService {

    public static boolean USE_SUBSET_BSSIDS = false;

    private final Map<String, Location> locationByIdentity;

    /**
     * Creates an instance of LocationService using the specified
     * InputStream to populate the locations.
     * Each line of the stream should contain the following entries:
     * <code>uniqueIdentity,cityName[,latitude,longitude,accessPointName,BSSID]+</code>
     * Malformed lines or lines with invalid latitudes or
     * longitudes cause creation to fail with an exception.
     * The first line and any line starting with the <code>#</code>
     * character are ignored.
     *
     * @param inputStream to populate the known locations;
     *                    stream will be closed on return
     */
    public LocationServiceImpl(InputStream inputStream) {
        if (inputStream == null) {
            throw new  IllegalArgumentException("InputStream may not be null");
        }
        locationByIdentity = new  TreeMap(String.CASE_INSENSITIVE_ORDER);
        int conditionObj0 = 2;
        try (BufferedReader reader = new  BufferedReader(new  InputStreamReader(inputStream))) {
            String line;
            boolean firstLine = true;
            while ((line = reader.readLine()) != null) {
                if (firstLine || line.startsWith("#")) {
                    firstLine = false;
                } else {
                    String[] parts = line.split(",");
                    if ((parts.length % 4) != conditionObj0) {
                        throw new  IllegalArgumentException("Location datastore contains a malformed line: " + line);
                    }
                    Set<AccessPoint> accessPoints = new  HashSet();
                    String identity = parts[0];
                    String cityName = parts[1];
                    for (int i = 2; i < parts.length; i += 4) {
                        double latitude = Double.valueOf(parts[i]);
                        double longitude = Double.valueOf(parts[i + 1]);
                        String name = parts[i + 2];
                        String bssid = parts[i + 3].toLowerCase();
                        accessPoints.add(new  AccessPoint(latitude, longitude, name, bssid));
                    }
                    Location location = new  Location(identity, cityName, accessPoints);
                    locationByIdentity.put(location.getIdentity(), location);
                }
            }
        } catch (IOException e) {
            throw new  IllegalArgumentException("Trouble parsing LocationService resources", e);
        }
    }

    @Override
    public Set<Location> getLocations() {
        return new  HashSet(locationByIdentity.values());
    }

    @Override
    public Location getLocation(String identity) {
        return locationByIdentity.get(identity);
    }

    @Override
    public Location getLocation(Set<String> bssids) {
        if ((bssids == null) || bssids.isEmpty()) {
            return null;
        }
        Set<String> copy = new  HashSet(bssids.size());
        for (String bssid : bssids) {
            getLocationHelper(bssid, copy);
        }
        return USE_SUBSET_BSSIDS ? getLocationUsingSubset(copy) : getLocationExactly(copy);
    }

    private Location getLocationExactly(Set<String> bssids) {
        for (Location location : locationByIdentity.values()) {
            if (location.getAccessPointBssids().equals(bssids)) {
                return location;
            }
        }
        return null;
    }

    private Location getLocationUsingSubset(Set<String> bssids) {
        for (Location location : locationByIdentity.values()) {
            if (location.getAccessPointBssids().containsAll(bssids)) {
                return location;
            }
        }
        return null;
    }

    private void getLocationHelper(String bssid, Set<String> copy) {
        copy.add(bssid.toLowerCase());
    }
}
