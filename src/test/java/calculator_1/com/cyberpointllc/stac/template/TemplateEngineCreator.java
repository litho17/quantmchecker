package calculator_1.com.cyberpointllc.stac.template;

public class TemplateEngineCreator {
    private String startTag = "\\{\\{";
    private String endTag = "\\}\\}";
    private String text;

    public TemplateEngineCreator assignStartTag(String startTag) {
        this.startTag = startTag;
        return this;
    }

    public TemplateEngineCreator defineEndTag(String endTag) {
        this.endTag = endTag;
        return this;
    }

    public TemplateEngineCreator fixText(String text) {
        this.text = text;
        return this;
    }

    public TemplateEngine composeTemplateEngine() {
        return new TemplateEngine(startTag, endTag, text);
    }
}