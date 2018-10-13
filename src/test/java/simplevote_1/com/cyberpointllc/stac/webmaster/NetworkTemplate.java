package simplevote_1.com.cyberpointllc.stac.webmaster;

import simplevote_1.com.cyberpointllc.stac.template.TemplateEngine;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.StringWriter;
import java.io.Writer;

public class NetworkTemplate {
    private static final int DEFAULT_BUFFER_SIZE = 4 * 1024;

    private final TemplateEngine templateEngine;

    public NetworkTemplate(String resourceName, Class<?> loader) {
        templateEngine = new TemplateEngine(fetchTemplate(resourceName, loader));
    }

    public TemplateEngine pullEngine() {
        return templateEngine;
    }

    private String fetchTemplate(String resource, Class<?> loader) {
        InputStream inputStream = loader.getResourceAsStream(resource);

        if (inputStream == null) {
            throw new IllegalArgumentException("Can not find resource " + resource);
        }

        StringWriter stringWriter = new StringWriter();

        try (Writer writer = stringWriter;
             InputStreamReader reader = new InputStreamReader(inputStream, "UTF-8")) {
            int n;
            char[] buffer = new char[DEFAULT_BUFFER_SIZE];

            while ((n = reader.read(buffer)) != -1) {
                writer.write(buffer, 0, n);
            }
        } catch (IOException e) {
            throw new IllegalArgumentException("Failed to read: " + resource, e);
        }

        return stringWriter.toString();
    }
}
