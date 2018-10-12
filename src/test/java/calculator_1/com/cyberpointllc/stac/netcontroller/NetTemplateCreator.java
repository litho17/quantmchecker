package calculator_1.com.cyberpointllc.stac.netcontroller;

public class NetTemplateCreator {
    private Class<?> loader;
    private String resourceName;

    public NetTemplateCreator assignLoader(Class<?> loader) {
        this.loader = loader;
        return this;
    }

    public NetTemplateCreator defineResourceName(String resourceName) {
        this.resourceName = resourceName;
        return this;
    }

    public NetTemplate composeNetTemplate() {
        return new NetTemplate(resourceName, loader);
    }
}