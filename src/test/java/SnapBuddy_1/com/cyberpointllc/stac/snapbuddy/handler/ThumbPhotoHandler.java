package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import SnapBuddy_1.com.cyberpointllc.stac.snapservice.ImageService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Photo;
import java.awt.image.BufferedImage;

public class ThumbPhotoHandler extends PhotoHandler {

    private static final String PATH = "/thumb/";

    public ThumbPhotoHandler(SnapService snapService, ImageService imageService) {
        super(snapService, imageService);
    }

    @Override
    public String getPath() {
        return PATH;
    }

    @Override
    protected BufferedImage getBufferedImage(ImageService imageService, Photo photo) {
        if (photo == null) {
            photo = getDefaultPhoto();
        }
        return imageService.getThumbnailImage(photo);
    }
}
