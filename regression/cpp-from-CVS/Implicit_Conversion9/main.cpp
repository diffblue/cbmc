enum foo {NOT_AFFECTED, FATAL_AFFECT, WARNING};

typedef struct {
  foo SeverityType;
} BitDatabaseRecordStruct;

const BitDatabaseRecordStruct BitDataBase [1] =
{
  {NOT_AFFECTED}
};

int main()
{
  return 0;
}

