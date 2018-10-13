package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

import simplevote_1.com.cyberpointllc.stac.webmaster.handler.HttpGuideResponse;
import com.sun.net.httpserver.HttpExchange;

import javax.imageio.ImageIO;
import java.awt.image.BufferedImage;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.net.URL;

public class IconGuide extends AbstractDirectVoteGuide {
    private static final String TRAIL = "/icon";
    private static final String IMAGE_TRAIL = "/images";
    private static final String IMAGE_FORM = "gif";
    private static final String MIME_TYPE = "image/gif";

    public IconGuide(DirectVoteHelper directVoteHelper) {
        super(directVoteHelper);
    }

    @Override
    public String takeTrail() {
        return TRAIL;
    }

    @Override
    public HttpGuideResponse handleObtain(HttpExchange httpExchange) {
        String remainingTrail = obtainRemainingTrail(httpExchange);

        if (remainingTrail == null) {
            return takeBadRequestResponse("Invalid Path: " + httpExchange.getRequestURI().getPath());
        }

        URL url = getClass().getResource(IMAGE_TRAIL + remainingTrail);

        if (url == null) {
            return takeBadRequestResponse("Could not find an image with the id " + remainingTrail);
        }

        HttpGuideResponse response;

        try (ByteArrayOutputStream stream = new ByteArrayOutputStream()) {
            BufferedImage bufferedImage = ImageIO.read(url);
            boolean success = ImageIO.write(bufferedImage, IMAGE_FORM, stream);

            if (success) {
                response = new IconGuideResponse(MIME_TYPE, stream.toByteArray());
            } else {
                response = takeBadRequestResponse("Could not convert the image into format " + IMAGE_FORM);
            }
        } catch (IOException e) {
            response = takeBadRequestResponse("Trouble converting the image: " + e.getMessage());
        }

        return response;
    }

    private static class IconGuideResponse extends HttpGuideResponse {
        private final String contentType;
        private final byte[] bytes;

        IconGuideResponse(String contentType, byte[] bytes) {
            this.contentType = contentType;
            this.bytes = bytes;
        }

        @Override
        protected String grabContentType() {
            return contentType;
        }

        @Override
        protected byte[] fetchResponseBytes(HttpExchange httpExchange) throws IOException {
            return bytes;
        }
    }
}
