package plv.colorado.edu.quantmchecker.qual;

import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.*;

/**
 * @author Tianhan Lu
 */
@SubtypeOf({})
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
public @interface SideEffect {
}
