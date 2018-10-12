package calculator_1.com.cyberpointllc.stac.netcontroller;

import calculator_1.com.cyberpointllc.stac.template.TemplateEngine;
import calculator_1.com.cyberpointllc.stac.template.TemplateEngineCreator;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.StringWriter;
import java.io.Writer;

public class NetTemplate {
    private static final int DEFAULT_BUFFER_CONTENT = 4 * 1024;

    private final TemplateEngine templateEngine;

    public NetTemplate(String resourceName, Class<?> loader) {
        templateEngine = new TemplateEngineCreator().fixText(grabTemplate(resourceName, loader)).composeTemplateEngine();
    }

    public TemplateEngine grabEngine() {
        return templateEngine;
    }

    private String grabTemplate(String resource, Class<?> loader) {
        InputStream inputStream = loader.getResourceAsStream(resource);

        if (inputStream == null) {
            throw new IllegalArgumentException("Can not find resource " + resource);
        }

        StringWriter stringWriter = new StringWriter();

        try (Writer writer = stringWriter;
             InputStreamReader reader = new InputStreamReader(inputStream, "UTF-8")) {
            int n;
            char[] buffer = new char[DEFAULT_BUFFER_CONTENT];

            while ((n = reader.read(buffer)) != -1) {
                writer.write(buffer, 0, n);
            }
        } catch (IOException e) {
            throw new IllegalArgumentException("Failed to read: " + resource, e);
        }

        return stringWriter.toString();
    }
}
