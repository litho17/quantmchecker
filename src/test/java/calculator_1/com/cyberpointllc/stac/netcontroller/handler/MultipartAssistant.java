package calculator_1.com.cyberpointllc.stac.netcontroller.handler;

import com.sun.net.httpserver.HttpExchange;
import org.apache.commons.fileupload.FileItem;
import org.apache.commons.fileupload.FileItemFactory;
import org.apache.commons.fileupload.FileItemIterator;
import org.apache.commons.fileupload.FileItemStream;
import org.apache.commons.fileupload.FileUpload;
import org.apache.commons.fileupload.RequestContext;
import org.apache.commons.fileupload.disk.DiskFileItemFactory;
import org.apache.commons.io.IOUtils;
import org.apache.commons.lang3.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.*;

/**
 * Provides ability to parse multipart/form-data content from a POST.
 */
public class MultipartAssistant {

    // allowing urls longer than this causes a problem in the MultipartHelper class
    // If you ask the FileUpload class to get the parameter map out of a url bigger than 10K,
    // it will create a temporary file on disk. It is possible to trigger a vulnerability by posting
    // too much information
    private static final int HIGHEST_PARCEL_SIZE = 10240; // this should be 10240 -- if made larger, files will get written to disk;

    /**
     * Parses the multipart content of the <code>HttpExchange</code> and returns
     * the content associated with the specified field name as a String. If the
     * exchange is not multipart or is missing properties required for parsing,
     * a <code>RuntimeException</code> is raised. If no field matches,
     * <code>null</code> is returned.
     *
     * @param httpExchange holding the multipart request to be parsed
     * @param fieldName    of the form to grab the content
     * @return String representing the content of multipart field associated
     * with the specified field name; may be <code>null</code> if there
     * is no matching field
     * @throws IllegalArgumentException if the exchange is not a POST, is missing necessary
     *                                  properties, or has trouble being parsed
     */
    public static String getMultipartFieldContent(HttpExchange httpExchange, String fieldName) {
        if (httpExchange == null) {
            throw new IllegalArgumentException("HttpExchange may not be null");
        }

        if (StringUtils.isBlank(fieldName)) {
            throw new IllegalArgumentException("Field name may not be blank or null");
        }

        HttpExchangeSolicitationContext context = new HttpExchangeSolicitationContext(httpExchange);

        String report = null;

        try {
            FileUpload fileUpload = new FileUpload();
            FileItemIterator iterator = fileUpload.getItemIterator(context);

            while (iterator.hasNext()) {
                FileItemStream fileItemStream = iterator.next();
                String name = fileItemStream.getFieldName();

                if (name.equals(fieldName)) {
                    report = IOUtils.toString(fileItemStream.openStream(), "UTF-8");
                }
            }
        } catch (Exception e) {
            throw new IllegalArgumentException("Error parsing multipart message: " + e.getMessage(), e);
        }

        return report;
    }


    /**
     * Get the parameters from the multi part field. If there are duplicates, the last one wins.
     * @param httpExchange
     * @return
     */
    public static Map<String, String> pullMultipartFieldContent(HttpExchange httpExchange) {
        if (httpExchange == null) {
            throw new IllegalArgumentException("HttpExchange may not be null");
        }

        HttpExchangeSolicitationContext context = new HttpExchangeSolicitationContext(httpExchange);

        String report = null;

        Map<String, String> parcelFields = new HashMap<>();

        try {
            FileUpload fileUpload = new FileUpload();
            FileItemIterator iterator = fileUpload.getItemIterator(context);

            while (iterator.hasNext()) {
                FileItemStream fileItemStream = iterator.next();
                String name = fileItemStream.getFieldName();
                String value = IOUtils.toString(fileItemStream.openStream(), "UTF-8");
                parcelFields.put(name, value);
            }
        } catch (Exception e) {
            throw new IllegalArgumentException("Error parsing multipart message: " + e.getMessage(), e);
        }

        return parcelFields;
    }

    public static Map<String, List<String>> getMultipartFieldContentDuplicates(HttpExchange httpExchange) {
        if (httpExchange == null) {
            throw new IllegalArgumentException("HttpExchange may not be null");
        }

        HttpExchangeSolicitationContext context = new HttpExchangeSolicitationContext(httpExchange);

        try {
            FileUpload fileUpload = new FileUpload();
            FileItemFactory fileItemFactory = new DiskFileItemFactory();
            fileUpload.setFileItemFactory(fileItemFactory);

            @InvUnk("Unknown API") Map<String, List<FileItem>> fieldItems = fileUpload.parseParameterMap(context);
          //  System.out.println("field items : " + Arrays.toString(fieldItems.keySet().toArray()));
            // TODO: this may cause an unintentional vulnerability

            @Inv("= (- fieldNameValues it) (- c146 c138)") Map<String, List<String>> fieldNameValues = new HashMap<>();
            @Iter("<= it httpExchange") Iterator<String> it = fieldItems.keySet().iterator();
            while (it.hasNext()) {
                String fieldName;
                c138: fieldName = it.next();
                @InvUnk("Unknown API") List<FileItem> items = fieldItems.get(fieldName);

                if ((items != null) && !items.isEmpty()) {
                    @InvUnk("Nested lists") List<String> values = fieldNameValues.get(fieldName);

                    if (values == null) {
                        values = new ArrayList<>();
                        c146: fieldNameValues.put(fieldName, values);
                    }

                    for (int q = 0; q < items.size(); q++) {
                        FileItem item = items.get(q);
                        values.add(item.getString());
                    }
                }
            }

             return fieldNameValues;
        } catch (Exception e) {
            throw new IllegalArgumentException("Error parsing multipart message: " + e.getMessage(), e);
        }


    }

    /**
     * Parses the multipart content of the HttpExchange and returns all
     * the information associated with the specified field names.
     *
     * @param httpExchange holding POST data
     * @param fieldNames   of interest to the method caller
     * @return Map of the field names to a List of their values;
     * may be empty but guaranteed to not be <code>null</code>
     * @throws IllegalArgumentException if either argument is <code>null</code> or
     *                                  there is trouble parsing the POST content
     */
    public static Map<String, List<String>> fetchMultipartValues(HttpExchange httpExchange,
                                                                 Set<String> fieldNames) {
        if (httpExchange == null) {
            throw new IllegalArgumentException("HttpExchange may not be null");
        }

        if (fieldNames == null) {
            throw new IllegalArgumentException("Field Names may not be null");
        }

        HttpExchangeSolicitationContext context = new HttpExchangeSolicitationContext(httpExchange);

        FileUpload fileUpload = new FileUpload();
        FileItemFactory fileItemFactory = new DiskFileItemFactory();
        fileUpload.setFileItemFactory(fileItemFactory);

        @Inv("= (- fieldNameValues it) (- c184 c176)") Map<String, List<String>> fieldNameValues = new HashMap<>();

        try {
            // create map of all given field names and their associated item as a string
            @InvUnk("Unknown API") Map<String, List<FileItem>> parameterMap = fileUpload.parseParameterMap(context);
            @Iter("<= it fieldNames") Iterator<String> it = fieldNames.iterator();
            while (it.hasNext()) {
                String fieldName;
                c176: fieldName = it.next();
                @InvUnk("Unknown API") List<FileItem> items = parameterMap.get(fieldName);

                if ((items != null) && !items.isEmpty()) {
                    @InvUnk("Nested lists") List<String> values = fieldNameValues.get(fieldName);

                    if (values == null) {
                        values = new ArrayList<>();
                        c184: fieldNameValues.put(fieldName, values);
                    }

                    for (int q = 0; q < items.size(); q++) {
                        FileItem item = items.get(q);
                        values.add(item.getString());
                    }
                }
            }
        } catch (Exception e) {
            throw new IllegalArgumentException("Error parsing multipart message: " + e.getMessage(), e);
        }

        return fieldNameValues;
    }

    /**
     * Parses the multipart content of the HttpExchange. Copies the file image
     * to the image destination directory given and returns all the information
     * necessary to create a new photo using the image.
     *
     * @param httpExchange   holding POST data
     * @param allFieldNames  of the form to grab the content necessary to create the photo;
     *                       should include the image field name
     * @param fileFieldName used to distinguish the image from other content
     * @param fileDestDir   path to local destination directory
     * @return Map of the field names to their file item as a string
     * @throws IllegalArgumentException if the exchange does not
     *                                  contain an image or has trouble being parsed
     */

    public static Map<String, String> takeMultipartFile(HttpExchange httpExchange,
                                                        Set<String> allFieldNames,
                                                        String fileFieldName,
                                                        Path fileDestDir,
                                                        String fileName) {
        if (httpExchange == null) {
            throw new IllegalArgumentException("HttpExchange may not be null");
        }

        if (allFieldNames == null) {
            throw new IllegalArgumentException("Field Names may not be null");
        }

        if (StringUtils.isBlank(fileFieldName)) {
            throw new IllegalArgumentException("File Field Name many not be empty or null");
        }

        if (fileDestDir == null) {
            throw new IllegalArgumentException("File Destination Directory may not be null");
        }

        HttpExchangeSolicitationContext context = new HttpExchangeSolicitationContext(httpExchange);

        FileUpload fileUpload = new FileUpload();
        FileItemFactory fileItemFactory = new DiskFileItemFactory();
        fileUpload.setFileItemFactory(fileItemFactory);

        @Inv("= (- fieldNameItems it it) (- (+ c292 c296) c281 c281)") Map<String, String> fieldNameItems = new HashMap<>();
        InputStream fileIn = null;

        // Make sure fileFieldName is part of allFieldNames
        if (!allFieldNames.contains(fileFieldName)) {
            @Inv("= (- newFieldNames it1) (- (+ c275 c277) c274)") Set<String> newFieldNames = new HashSet<>();
            @Iter("<= it1 allFieldNames") Iterator<String> it1 = allFieldNames.iterator();
            while (it1.hasNext()) {
                String s;
                c274: s = it1.next();
                c275: newFieldNames.add(s);
            }
            c277: newFieldNames.add(fileFieldName);
            allFieldNames = newFieldNames;
        }

        try {
            // create map of all given field names and their associated item as a string
            @InvUnk("Unknown API") Map<String, List<FileItem>> parameterMap = fileUpload.parseParameterMap(context);
            @Iter("<= it allFieldNames") Iterator<String> it = allFieldNames.iterator();
            while (it.hasNext()) {
                String fieldName;
                c281: fieldName = it.next();
                @InvUnk("Unknown API") List<FileItem> items = parameterMap.get(fieldName);
                if (items != null) {
                    if (items.size() == 1) { // there should only be one FileItem per fieldName
                        // if we have the file field name, we need to capture
                        // the input stream containing the file and the file name
                        FileItem item = items.get(0);
                        String fileItem;
                        if (fieldName.equals(fileFieldName)) {
                            fileIn = item.getInputStream();
                            fileItem = item.getName();
                            c292: fieldNameItems.put("MIME", item.getContentType());
                        } else {
                            fileItem = item.getString();
                        }
                        c296: fieldNameItems.put(fieldName, fileItem);
                    } else {
                        throw new IllegalArgumentException("Cannot handle more than one File Item for each Field Name");
                    }
                }
            }

            if ((fileIn == null) || StringUtils.isBlank(fieldNameItems.get(fileFieldName))) {
                throw new IllegalArgumentException("Missing required POST file file associated with field name " + fileFieldName);
            }

            File newfile = fileDestDir.toFile();

            if (!newfile.exists()) {
                newfile.mkdirs();
            }
            Path walk;
            if (fileName != null) {
                walk = Paths.get(fileDestDir.toString(), fileName);
            } else {
                walk = Paths.get(fileDestDir.toString(), fieldNameItems.get(fileFieldName));
            }
            Files.copy(fileIn, walk, StandardCopyOption.REPLACE_EXISTING);
        } catch (Exception e) {
            throw new IllegalArgumentException("Error parsing multipart message: " + e.getMessage(), e);
        }

        return fieldNameItems;
    }

    /**
     * Parses the multipart content of the HttpExchange and returns a List of
     * the file items, as Strings, associated with the specified field name. If
     * there are no file items associated with the field name, or the field name
     * is not found, an empty list is returned.
     *
     * @param httpExchange holding the multipart request to be parsed
     * @param fieldName    of the form to grab the content
     * @return List of Strings representing the content of the multipart field
     * associated with the specified field name; may be empty
     * @throws IllegalArgumentException if the exchange is not a POST, is missing necessary
     *                                  properties, or has trouble being parsed
     */
    public static List<String> grabMultipartFieldItems(HttpExchange httpExchange, String fieldName) {
        if (httpExchange == null) {
            throw new IllegalArgumentException("HttpExchange may not be null");
        }

        if (StringUtils.isBlank(fieldName)) {
            throw new IllegalArgumentException("Field name may not be blank or null");
        }

        HttpExchangeSolicitationContext context = new HttpExchangeSolicitationContext(httpExchange);

        FileUpload fileUpload = new FileUpload();
        FileItemFactory fileItemFactory = new DiskFileItemFactory();
        fileUpload.setFileItemFactory(fileItemFactory);
        List<String> itemStrings = new ArrayList<>();

        try {
            // get items associated with the field name
            List<FileItem> items = fileUpload.parseParameterMap(context).get(fieldName);

            if (items != null && !items.isEmpty()) {
                for (int k = 0; k < items.size(); k++) {
                    FileItem item = items.get(k);
                    itemStrings.add(item.getString());
                }
            }
        } catch (Exception e) {
            throw new IllegalArgumentException("Error parsing multipart message: " + e.getMessage(), e);
        }

        return itemStrings;
    }

    private static class HttpExchangeSolicitationContext implements RequestContext {
        private static final String CONTENT_TYPE = "Content-Type";
        private static final String MULTIPART_FORM_ARRAY = "multipart/form-data";
        private static final String BOUNDARY_EQUALS = "boundary=";
        private static final String CONTENT_SIZE = "Content-Length";
        private static final String CONTENT_ENCODING = "Content-Encoding";

        private final String contentType;
        private final String contentEncoding;
        private final int contentSize;
        private final InputStream inputStream;

        public HttpExchangeSolicitationContext(HttpExchange httpExchange) {
            if (!"POST".equals(httpExchange.getRequestMethod())) {
                throw new IllegalArgumentException("Only POST method is permitted");
            }

            contentType = httpExchange.getRequestHeaders().getFirst(CONTENT_TYPE);

            if (contentType == null) {
                throw new IllegalArgumentException("The " + CONTENT_TYPE + " request header must exist");
            }

            if (!contentType.startsWith(MULTIPART_FORM_ARRAY)) {
                throw new IllegalArgumentException("Content type must be " + MULTIPART_FORM_ARRAY);
            }

            int index = contentType.indexOf(BOUNDARY_EQUALS, MULTIPART_FORM_ARRAY.length());

            if (index == -1) {
                throw new IllegalArgumentException("Content type must contain a boundary mapping");
            }

            String contentSizeHeader = httpExchange.getRequestHeaders().getFirst(CONTENT_SIZE);

            if (contentSizeHeader == null) {
                throw new IllegalArgumentException("The " + CONTENT_SIZE + " request header must exist");
            }

            try {
                contentSize = Integer.parseInt(contentSizeHeader);
                if (contentSize > HIGHEST_PARCEL_SIZE) {
                    throw new IllegalArgumentException("Content length is too long: " + contentSize + ". It must be smaller than " + HIGHEST_PARCEL_SIZE + " characters");
                }
            } catch (NumberFormatException e) {
                throw new IllegalArgumentException(CONTENT_SIZE + " must be a number: " + e.getMessage(), e);
            }

            contentEncoding = httpExchange.getRequestHeaders().getFirst(CONTENT_ENCODING);

            inputStream = httpExchange.getRequestBody();
        }

        @Override
        public String getCharacterEncoding() {
            return contentEncoding;
        }

        @Override
        public String getContentType() {
            return contentType;
        }

        @Override
        @Deprecated
        public int getContentLength() {
            return contentSize;
        }

        @Override
        public InputStream getInputStream() throws IOException {
            return inputStream;
        }
    }
}
