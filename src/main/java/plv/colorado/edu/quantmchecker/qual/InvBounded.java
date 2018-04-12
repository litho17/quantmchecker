package plv.colorado.edu.quantmchecker.qual;

import org.checkerframework.framework.qual.DefaultFor;
import org.checkerframework.framework.qual.DefaultQualifierInHierarchy;
import org.checkerframework.framework.qual.SubtypeOf;
import org.checkerframework.framework.qual.TypeUseLocation;

import java.lang.annotation.*;

/**
 * @author Tianhan Lu
 */
// @DefaultQualifierInHierarchy
// @DefaultFor({TypeUseLocation.FIELD, TypeUseLocation.LOCAL_VARIABLE, TypeUseLocation.PARAMETER})
@SubtypeOf({InvTop.class})
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
@Documented
public @interface InvBounded {
}
