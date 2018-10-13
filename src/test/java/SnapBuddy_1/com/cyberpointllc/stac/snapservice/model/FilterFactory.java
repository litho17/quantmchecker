package SnapBuddy_1.com.cyberpointllc.stac.snapservice.model;

import SnapBuddy_1.com.jhlabs.image.BicubicScalingFilter;
import SnapBuddy_1.com.jhlabs.image.ChromeFilter;
import SnapBuddy_1.com.jhlabs.image.ContrastFilter;
import SnapBuddy_1.com.jhlabs.image.CrystallizeFilter;
import SnapBuddy_1.com.jhlabs.image.CurlFilter;
import SnapBuddy_1.com.jhlabs.image.DespeckleFilter;
import SnapBuddy_1.com.jhlabs.image.EdgeFilter;
import SnapBuddy_1.com.jhlabs.image.EmbossFilter;
import SnapBuddy_1.com.jhlabs.image.FlipFilter;
import SnapBuddy_1.com.jhlabs.image.GaussianFilter;
import SnapBuddy_1.com.jhlabs.image.GrayscaleFilter;
import SnapBuddy_1.com.jhlabs.image.InvertFilter;
import SnapBuddy_1.com.jhlabs.image.KaleidoscopeFilter;
import SnapBuddy_1.com.jhlabs.image.MinimumFilter;
import SnapBuddy_1.com.jhlabs.image.OilFilter;
import SnapBuddy_1.com.jhlabs.image.RescaleFilter;
import SnapBuddy_1.com.jhlabs.image.SmearFilter;
import SnapBuddy_1.com.jhlabs.image.SolarizeFilter;
import SnapBuddy_1.com.jhlabs.image.SwimFilter;
import SnapBuddy_1.com.jhlabs.image.TritoneFilter;
import SnapBuddy_1.com.jhlabs.image.TwirlFilter;
import java.util.Collection;
import java.util.Map;
import java.util.TreeMap;

public class FilterFactory {

    private static final Map<String, Filter> filters = new  TreeMap(String.CASE_INSENSITIVE_ORDER);

    static {
        addFilter(new  Filter("F000", "Emboss", new  EmbossFilter()));
        addFilter(new  Filter("F001", "Constrast", new  ContrastFilter()));
        addFilter(new  Filter("F002", "Grayscale", new  GrayscaleFilter()));
        addFilter(new  Filter("F003", "Invert", new  InvertFilter()));
        addFilter(new  Filter("F004", "Rescale", new  RescaleFilter(3)));
        addFilter(new  Filter("F005", "Tritone", new  TritoneFilter()));
        addFilter(new  Filter("F006", "Flip", new  FlipFilter()));
        addFilter(new  Filter("F007", "Kaleidoscope", new  KaleidoscopeFilter()));
        addFilter(new  Filter("F008", "Swim", new  SwimFilter()));
        addFilter(new  Filter("F009", "Twirl", new  TwirlFilter()));
        addFilter(new  Filter("F00A", "Chrome", new  ChromeFilter()));
        addFilter(new  Filter("F00B", "Crystallize", new  CrystallizeFilter()));
        addFilter(new  Filter("F00C", "Smear", new  SmearFilter()));
        addFilter(new  Filter("F00D", "Minimum", new  MinimumFilter()));
        addFilter(new  Filter("F00E", "ScaleUp", new  BicubicScalingFilter(2.0, 2.0)));
        addFilter(new  Filter("F00F", "OilPainting", new  OilFilter()));
        addFilter(new  Filter("F010", "Curl", new  CurlFilter()));
        addFilter(new  Filter("F011", "Edge", new  EdgeFilter()));
        addFilter(new  Filter("F012", "Solarize", new  SolarizeFilter()));
        addFilter(new  Filter("F013", "GaussianBlur", new  GaussianFilter()));
        addFilter(new  Filter("F014", "Despeckle", new  DespeckleFilter()));
        addFilter(new  Filter("F015", "ScaleDown", new  BicubicScalingFilter(0.5, 0.5)));
    }

    private static void addFilter(Filter filter) {
        filters.put(filter.getIdentity(), filter);
    }

    private FilterFactory() {
    }

    /**
     * Returns all the filters that have been created.
     *
     * @return Collection<Filter> the filters that have been created
     */
    public static Collection<Filter> getFilters() {
        return filters.values();
    }

    /**
     * Retrieves a specific filter given its id.
     *
     * @param id of the filter
     * @return Filter associated with the id
     */
    public static Filter getFilter(String id) {
        return filters.get(id);
    }
}
