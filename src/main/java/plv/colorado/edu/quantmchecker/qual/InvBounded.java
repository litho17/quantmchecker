package plv.colorado.edu.quantmchecker.qual;

import org.checkerframework.framework.qual.DefaultQualifierInHierarchy;
import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.*;

/**
 * @author Tianhan Lu
 */
//@DefaultQualifierInHierarchy
@SubtypeOf({InvTop.class})
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.LOCAL_VARIABLE, ElementType.FIELD})
@Documented
public @interface InvBounded {
}
