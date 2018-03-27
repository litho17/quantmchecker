package plv.colorado.edu.quantmchecker.qual;

import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.*;

/**
 * @author Tianhan Lu
 */
@SubtypeOf({SumTop.class})
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@Documented
public @interface Summary {
    String[] value();
}
