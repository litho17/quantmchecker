package calculator_1.com.cyberpointllc.stac.netcontroller.persist;

import org.mapdb.Serializer;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;
import java.time.LocalDateTime;

public class LocalDateTimeDigitizer extends Serializer<LocalDateTime> {

    @Override
    public void serialize(DataOutput out, LocalDateTime localDateTime) throws IOException {

        // Order of LocalDateTime Serialization: Year,Month,Day,Hour,Min,Sec,NanoSec
        out.writeInt(localDateTime.getYear());
        out.writeInt(localDateTime.getMonthValue());
        out.writeInt(localDateTime.getDayOfMonth());
        out.writeInt(localDateTime.getHour());
        out.writeInt(localDateTime.getMinute());
        out.writeInt(localDateTime.getSecond());
        out.writeInt(localDateTime.getNano());

    }

    @Override
    public LocalDateTime deserialize(DataInput in, int available) throws IOException {

        int year = in.readInt();
        int month = in.readInt();
        int day = in.readInt();
        int hour = in.readInt();
        int minute = in.readInt();
        int second = in.readInt();
        int nanoSecond = in.readInt();

        return LocalDateTime.of(year,month,day,hour,minute,second,nanoSecond);
    }
}
