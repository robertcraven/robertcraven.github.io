var totalCount = 15;
function ChangeIt()
{
 var num = Math.floor(Math.random() * (totalCount + 1));
 if (num < 10) {
  document.body.background = 'bgimages/0'+num+'.jpg';
 } else {
  document.body.background = 'bgimages/'+num+'.jpg';
 }
}
