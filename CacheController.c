//Cache Controller
//DHWAJ VANDANKUMAR JANI
//all cholesky inputs are defined in header file input.h
#include <stdio.h>
#include <math.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>
#include "input.h"
#define  Max_Ways 16
#define  Max_Lines 131072
#define Cache_Size 262144
#define width 2
bool Valid[Max_Lines][Max_Ways];
bool Dirty[Max_Lines][Max_Ways];
uint8_t LRU[Max_Lines][Max_Ways];
uint32_t tag[Max_Lines][Max_Ways];
uint32_t Total_Bytes_Wr = 0, Total_Bytes_Rd = 0, Read_Memory_count = 0, Write_Memory_count = 0;
uint32_t Rd_Cache_Count = 0, Rd_Cache_Hit_Count = 0, Rd_Cache_Miss_Count = 0, Wr_Cache_Count = 0, Wr_Cache_Hit_Count = 0,Wr_Cache_Miss_Count = 0 ;
uint32_t  Rd_WrBack_Dirty_Count = 0, Rd_Replace_Count = 0, Wr_Replace_Count = 0, Wr_WrBack_Dirty_Count =0;
uint32_t Wr_Through_memory =0, Rd_RdMemToCache_Count = 0, Wr_RdMemToCache_Count = 0, Flush_Count = 0, Write_CputoCache_Count =0, Read_CacheToCPU_Count = 0;
uint8_t Write_stratergy = 0, excel_row_count = 2;
enum  Write_Strat{WB,WTA,WTNA};
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// //INPUTS
//cholesky inputs are in input.h
#pragma align 16(y)
uint64_t y[98304];
#pragma align 16(data)
uint8_t data[524288];

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//CHOLESKY FUNCTIONS
void choldc(double** a, int n, double p[], uint32_t ways, uint32_t bl )
{
//void nrerror(char error_text[]);
//All parameters thatare passed to the function i.e. a,p & matrix size are assumed to be in register
#pragma align 16(sum)
double sum;
int i,j,k; 
Write_Memory(&i,4,ways,bl);
for (i=0;i<n;i++) 
{
Read_Memory(&i,4,ways,bl);
Write_Memory(&j,4,ways,bl);
for (j=i;j<n;j++) 
{
Read_Memory(&i,4,ways,bl);
Read_Memory(&a[i],4,ways,bl);
Read_Memory(&j,4,ways,bl);
Read_Memory(&a[i][j],8,ways,bl);
Write_Memory(&sum,8,ways,bl);
Read_Memory(&i,4,ways,bl);
Write_Memory(&k,4,ways,bl);
for (sum=a[i][j],k=i-1;k>=0;k--) 
    {
      sum -= a[i][k]*a[j][k];
      Read_Memory(&i,4,ways,bl);
      Read_Memory(&a[i],4,ways,bl);
      Read_Memory(&k,4,ways,bl);
      Read_Memory(&a[i][k],8,ways,bl);
      Read_Memory(&j,4,ways,bl);
      Read_Memory(&a[j],4,ways,bl);
      Read_Memory(&k,4,ways,bl);
      Read_Memory(&a[j][k],8,ways,bl);
      Read_Memory(&sum,8,ways,bl);
      Write_Memory(&sum,8,ways,bl);
      /////////////////////////////
      Read_Memory(&k,4,ways,bl);
      Write_Memory(&k,4,ways,bl);
    }
Read_Memory(&i,4,ways,bl);
Read_Memory(&j,4,ways,bl);
if (i == j) 
{
 Read_Memory(&sum,8,ways,bl);
 if (sum <= 0.0) //a, with rounding errors, is not positive definite.
    {
      printf("choldc failed");
      break;
    }
p[i]=sqrt(sum);
Read_Memory(&sum,8,ways,bl);
Read_Memory(&i,4,ways,bl);
Write_Memory(&p[i],8,ways,bl);
} 
else 
{
a[j][i]=sum/p[i];
Read_Memory(&sum,8,ways,bl);
Read_Memory(&i,4,ways,bl);
Read_Memory(&p[i],8,ways,bl);
Read_Memory(&j,4,ways,bl);
Read_Memory(&a[j],4,ways,bl);
Read_Memory(&i,4,ways,bl);
Write_Memory(&a[j][i],8,ways,bl);
}
Read_Memory(&j,4,ways,bl);
Write_Memory(&j,4,ways,bl);
}
Read_Memory(&i,4,ways,bl);
Write_Memory(&i,4,ways,bl);
}
}

void cholsl(double **a, int n, double p[], double b[], double x[], uint32_t ways, uint32_t bl)
{
//All parameters thatare passed to the function i.e. a,p,b,x & matrix size are assumed to be in register
#pragma align 16(sum)
double sum;
int i,k;
Write_Memory(&i,4,ways,bl);
for (i=0;i<n;i++) //Solve L · y = b, storing y in x.
{ 
Read_Memory(&i,4,ways,bl);
Read_Memory(&b[i],8,ways,bl);
Write_Memory(&sum,8,ways,bl);
Read_Memory(&i,4,ways,bl);
Write_Memory(&k,4,ways,bl);
for (sum=b[i],k=i-1;k>=0;k--) 
{
  sum -= a[i][k]*x[k];
  Read_Memory(&i,4,ways,bl);
  Read_Memory(&a[i],4,ways,bl);
  Read_Memory(&k,4,ways,bl);
  Read_Memory(&a[i][k],8,ways,bl);
  Read_Memory(&k,4,ways,bl);
  Read_Memory(&x[k],8,ways,bl);
  Read_Memory(&sum,8,ways,bl);
  Write_Memory(&sum,8,ways,bl);
  ///////////////////////////////////////////
  Read_Memory(&k,4,ways,bl);
  Write_Memory(&k,4,ways,bl);
}
x[i]=sum/p[i];
Read_Memory(&sum,8,ways,bl);
Read_Memory(&i,4,ways,bl);
Read_Memory(&p[i],8,ways,bl);
Read_Memory(&i,4,ways,bl);
Write_Memory(&x[i],8,ways,bl);
/////////////////////////////////
Read_Memory(&i,4,ways,bl);
Write_Memory(&i,4,ways,bl);
}
Write_Memory(&i,4,ways,bl);
for (i=n-1;i>=0;i--)
{
Read_Memory(&i,4,ways,bl);
Read_Memory(&x[i],8,ways,bl);
Write_Memory(&sum,8,ways,bl);
Read_Memory(&i,4,ways,bl);
Write_Memory(&k,4,ways,bl);
for (sum=x[i],k=i+1;k<n;k++) 
{
  sum -= a[k][i]*x[k];
  Read_Memory(&k,4,ways,bl);
  Read_Memory(&a[k],4,ways,bl);
  Read_Memory(&i,4,ways,bl);
  Read_Memory(&a[k][i],8,ways,bl);
  Read_Memory(&k,4,ways,bl);
  Read_Memory(&x[k],8,ways,bl);
  Read_Memory(&sum,8,ways,bl);
  Write_Memory(&sum,8,ways,bl);
  /////////////////////////////////////
  Read_Memory(&k,4,ways,bl);
  Write_Memory(&k,4,ways,bl);
}
x[i]=sum/p[i];
Read_Memory(&sum,8,ways,bl);
Read_Memory(&i,4,ways,bl);
Read_Memory(&p[i],8,ways,bl);
Read_Memory(&i,4,ways,bl);
Write_Memory(&x[i],8,ways,bl);
/////////////////////////////////////////
Read_Memory(&i,4,ways,bl);
Write_Memory(&i,4,ways,bl);
}
}


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void zero_cache(uint8_t n, uint8_t bl)
{
  uint32_t No_of_lines = Cache_Size / (n*bl*width);
  for(uint32_t i=0; i<No_of_lines; i++)
  {
    for(uint8_t j=0; j<n; j++)
    {
      Valid[i][j] = false;
      Dirty[i][j] = false;
      LRU[i][j] = j;
    }
  }
  Total_Bytes_Wr = 0;
  Total_Bytes_Rd = 0 ;
  Read_Memory_count = 0;
  Write_Memory_count = 0;
  Rd_Cache_Count = 0;
  Rd_Cache_Hit_Count = 0; 
  Rd_Cache_Miss_Count = 0;
  Rd_Replace_Count = 0;
  Rd_WrBack_Dirty_Count = 0;
  Read_CacheToCPU_Count = 0;
  Wr_Cache_Count = 0;
  Wr_Cache_Hit_Count = 0; 
  Wr_Cache_Miss_Count = 0;
  Wr_Replace_Count = 0;
  Wr_WrBack_Dirty_Count = 0;
  Write_CputoCache_Count = 0;
  Wr_Through_memory = 0;
  Rd_RdMemToCache_Count = 0;
  Wr_RdMemToCache_Count = 0;
  Flush_Count = 0;
}

uint32_t get_line(void* pmem, uint32_t n, uint32_t bl)
{
   uint32_t L, l, B, b, line;
   uint32_t add = ((uint32_t) pmem);
    B = bl * width;
    b = log2(B);
    L = Cache_Size / (n * B);
    l = log2(L);
    line = ( add >> b) & (0xFFFFFFFF >> (32 - l));
    return line;
}

uint32_t get_tag(void* pmem, uint32_t n, uint32_t bl)
{
   uint32_t L, l, B, b, tag;
   uint32_t add = (uint32_t) pmem;
    B = bl * width;
    b = log2(B);
    L = Cache_Size / (n * B);
    l = log2(L);
    tag = ((add & 0xFFFFFF) >> (b+l));
    return tag;
}

int8_t Find_Tag(uint32_t line, uint32_t Tag, uint32_t n)  //To find if Hit or not
{
  int way = -1;
  for(uint8_t i=0; i<n; i++)
  {
      if((tag[line][i] == Tag) && (Valid[line][i]))
        {
          way = i; break;
        }
  }
 return way;
}

void Set_tag(uint32_t line, int8_t way, uint32_t Tag)
{
  tag[line][way] = Tag;
}

int8_t Find_Invalid_way(uint32_t line,uint8_t n)
{
  for(uint8_t i=0; i<n ; i++)
  {
    if(Valid[line][i] == false)
       return i;
  }
  return -1;
}

int8_t Find_oldest_LRU(uint32_t line, uint8_t n)
{
 for(uint8_t i=0; i<n ; i++)
 {
   if(LRU[line][i] == n-1)
      return i;
 } 
 return -1;
}

void UpdateLRUs(uint32_t line, int8_t way, uint8_t n)
{
  for(uint8_t i=0; i<n ; i++)
  {
    if((i != way) && (LRU[line][i] < LRU[line][way]))
       LRU[line][i]++;
  }
  LRU[line][way] = 0;
}

bool IsDirty(uint32_t line, int8_t way)
{
  return(Dirty[line][way]);
}
void InValidate(uint32_t line, int8_t way)
{
  Valid[line][way] = false;
}

void Validate(uint32_t line, int8_t way)
{
  Valid[line][way] = true;
}

void WriteThroughMemory(uint32_t size)
{
      Wr_Through_memory += (size + (size%width))/width;
}

void Write_Block_Dirty(uint32_t line,int8_t way)
{
  Dirty[line][way] = false;
}

Write_Cache_from_CPU(uint32_t line,uint32_t way)
{
  Write_CputoCache_Count++;
}

void Read_Meomory_to_Cache(uint32_t line,int8_t way){}

void Read_Cache_to_CPU(uint32_t line,int8_t way)
{
  Read_CacheToCPU_Count++;
}

void Read_Cache(void* pmem, uint32_t n, uint32_t bl)
{
  uint32_t add = (uint32_t) pmem;
  uint32_t line = get_line(add, n, bl);
  uint32_t tag = get_tag(add, n, bl);
  int8_t way = Find_Tag(line, tag, n);
  bool hit = (way != -1);
  if(!hit)
  {
    way = Find_Invalid_way(line,n);
    if( way == -1)  // if no invalid(Empty) way found then replace
    {
    way = Find_oldest_LRU(line, n);
    Rd_Replace_Count++;
    if(IsDirty(line,way))
    {
      Rd_WrBack_Dirty_Count++;
      Write_Block_Dirty(line,way);  //write dirty block back to memory
    }
    InValidate(line,way);
    }
    Set_tag(line,way,tag);
    Read_Meomory_to_Cache(line,way);
    Rd_RdMemToCache_Count++;
    Validate(line, way); 
  }
  UpdateLRUs(line, way, n);
  Rd_Cache_Count++;
  Read_Cache_to_CPU(line,way);
  if(hit)
     Rd_Cache_Hit_Count++;
  else
     Rd_Cache_Miss_Count++;
}

void Read_Memory(void* pmem, uint32_t size, uint32_t n, uint32_t bl)
{
 int32_t Last_line = -1;
 uint32_t line;
 uint32_t add = (uint32_t) pmem;
 for(uint32_t i=0; i<size; i++)
 {
   line = get_line(add,n,bl);
   if(line != Last_line)
   {
     Read_Cache(add,n,bl);
     Last_line = line;
   }
   add++;
 }
 Total_Bytes_Rd += size;
 Read_Memory_count++;
}

void Write_Cache(void* pmem, uint32_t n, uint32_t bl)
{
  uint32_t d;
  uint32_t add = (uint32_t) pmem;
  Wr_Cache_Count++;
  uint32_t line = get_line(add, n, bl);
  uint32_t tag = get_tag(add, n, bl);
  int8_t way = Find_Tag(line, tag, n);
  bool hit = (way != -1);
  if(!hit  &&  (Write_stratergy != WTNA))
  {
    way = Find_Invalid_way(line,n);
    if( way == -1)  // if no invalid way found then replace
    {
    way = Find_oldest_LRU(line, n);
    Wr_Replace_Count++;
    if(IsDirty(line,way))
    {
      Wr_WrBack_Dirty_Count++;
      Write_Block_Dirty(line,way); //write dirty block back to memory
    }
    InValidate(line,way);
    }
    Set_tag(line,way,tag);
    Read_Meomory_to_Cache(line,way); //Read a block from memory to cache
    Wr_RdMemToCache_Count++;
    Validate(line, way); 
  }

  if((Write_stratergy != WTNA) || hit)
  {
  UpdateLRUs(line, way, n);
  Write_Cache_from_CPU(line,way);
  }

   if(Write_stratergy == WB)
   {
     Dirty[line][way] = true;
   }

  if(hit)
     Wr_Cache_Hit_Count++;
  else
     Wr_Cache_Miss_Count++;
}


void Write_Memory(void* pmem, uint32_t size, uint32_t n, uint32_t bl)
{
 int32_t Last_line = -1;
 uint32_t line;
 uint32_t add = (uint32_t) pmem;
 for(uint32_t i=0; i<size; i++)
 {
   line = get_line(add,n,bl);
   if(line != Last_line)
   {
     Write_Cache(add,n,bl);
     Last_line = line;
   }
   add++;
 }
 if(Write_stratergy == WTA || Write_stratergy == WTNA)
 {
    WriteThroughMemory(size);
 }
 Total_Bytes_Wr += size;
 Write_Memory_count++;
}

void Flush_Cache(uint32_t n, uint32_t bl)
{
  uint32_t No_of_lines = Cache_Size / (n*bl*width);
  for(uint32_t i=0; i<No_of_lines; i++)
  {
    for(uint8_t j=0; j<n; j++)
    {
      if(Dirty[i][j])
        Flush_Count++;
    }
  }
}

void Print_Results(uint32_t n, uint32_t bl)
{
  FILE * fp;
  char read_time[100],wb_time[100], Total_Write_Time[100], Flush_Time[100], Total_Time[100], Time_Sec[50], WR_St[5];
   if(n==1 && bl==1 && Write_stratergy==WB)
      {
      fp = fopen ("results.xls", "w");
       fprintf(fp,"%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s",
       "n",
        "Burst Length",
        "Write_stratergy",
        "Read_Memory_count",
        "Total_Bytes_Rd",
        "Rd_Cache_Count",
        "Rd_Cache_Hit_Count",
        "Rd_Cache_Miss_Count",
        "Rd_Replace_Count",
        "Read_CacheToCPU_Count",
        "Rd_WrBack_Dirty_Count",
        "Rd_RdMemToCache_Count",
        "Write_Memory_count",
        "Total_Bytes_Wr",
        "Wr_Cache_Count",
        "Wr_Cache_Hit_Count",
        "Wr_Cache_Miss_Count",
        "Wr_Replace_Count",
        "Write_CputoCache_Count",
        "Wr_WrBack_Dirty_Count",
        "Wr_RdMemToCache_Count",
        "Wr_Through_memory",
        "Flush_Count",
        "Total Read Time",
        "Write Cache Time",
        "Total Write time",
        "Flush Time",
        "Total Time",
        "AMAT Seconds");
      }
  else
       fp = fopen ("results.xls", "a");
  switch(Write_stratergy){
  case 0: strcpy(WR_St, "WB");break;
  case 1: strcpy(WR_St, "WTA");break;
  case 2: strcpy(WR_St, "WTNA");break; default:;}
  sprintf(read_time,"=J%d+((L%d+K%d)*(90+((B%d-1)*15)))",excel_row_count,excel_row_count,excel_row_count,excel_row_count); //formula for excel cell
  sprintf(wb_time,"=S%d+((U%d+T%d)*(90+((B%d-1)*15)))",excel_row_count,excel_row_count,excel_row_count,excel_row_count);  //formula for excel cell
  sprintf(Total_Write_Time,"=MAX(Y%d,(90*V%d))",excel_row_count,excel_row_count,excel_row_count);
  sprintf(Flush_Time,"=W%d*(90+((B%d-1)*15))",excel_row_count,excel_row_count);
  sprintf(Total_Time,"=X%d+Z%d+AA%d",excel_row_count,excel_row_count,excel_row_count);
  sprintf(Time_Sec,"=AB%d/1e9",excel_row_count);
  excel_row_count++;
  fprintf(fp,"\n%lu\t%lu\t%s\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%lu\t%s\t%s\t%s\t%s\t%s\t%s",
  n,
  bl,
  WR_St,
  Read_Memory_count,
  Total_Bytes_Rd,
  Rd_Cache_Count,
  Rd_Cache_Hit_Count,
  Rd_Cache_Miss_Count,
  Rd_Replace_Count,
  Read_CacheToCPU_Count,
  Rd_WrBack_Dirty_Count,
  Rd_RdMemToCache_Count,
  Write_Memory_count,
  Total_Bytes_Wr,
  Wr_Cache_Count,
  Wr_Cache_Hit_Count,
  Wr_Cache_Miss_Count,
  Wr_Replace_Count,
  Write_CputoCache_Count,
  Wr_WrBack_Dirty_Count,
  Wr_RdMemToCache_Count,
  Wr_Through_memory,
  Flush_Count,
  read_time,
  wb_time,
  Total_Write_Time,
  Flush_Time,
  Total_Time,
  Time_Sec);
  fclose(fp);
}

int main()
{ 
  uint32_t n , bl, m,i;
  uint32_t d=0, f=0;
  uint8_t test;
   m = 256;
  while(d <= (m*m))
  {
    ptr[f++] = &a[d];
    d = d+m;
  }
  test = 0; //0 to run cholesky functions
  for(Write_stratergy=WB; Write_stratergy<=WTNA; Write_stratergy++)
  {
  for(n=1;n<17;n=n*2)
  { 
  for(bl=1;bl<9;bl=bl*2)
  {
  zero_cache(n,bl);
  switch(test)
  {
  case 0: choldc(ptr,m,p,n,bl);      //cholesky calls
          cholsl(ptr,m,p,b,x,n,bl);
          break;
  case 1: for(i=0; i<524288; i++)       //test case
          {
            data[i] = 0;
            Write_Memory(&data[i], 1, n, bl);
          }
          break;
  case 2: for(i=0; i<16; i++)           //test case
          {
            y[i] = 0;
            Write_Memory(&y[i], 8, n, bl);
          }
          break;
  default: d = d;//do nothing
  }
  Flush_Cache(n,bl);
  Print_Results(n,bl);
  }
  }
  }
   for(d=0;d<m;d++)
      printf("%f   ",x[d]);
  return 0;
}
